import Towers.Group.BidegreeTraceSpecialization

open scoped commutatorElement

namespace Towers
namespace PPColl
namespace RCColl

/-- Turn a normalized local collection into a refinement of the normalized
source factor.  The accumulated exponents enter only here, through the
arithmetic composition lemma `RCFlow.good`. -/
def withoutConjugatorRefinement
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {F : RFactor G}
    (C : RCColl p x y F.word F.multiplicity)
    (hF : F.Good p a b) :
    RFactor.Refa p a (b + 1) x y x (y ^ p)
      F.withoutConjugator where
  factors := C.factors
  eval_eq := by
    simpa using C.eval_eq
  factors_good :=
    RCFlow.forall_good hF C.factors_flow

/-- Restore the source factor's arbitrary outer conjugator after normalized
collection. -/
def toRefa
    {p a b : ℕ}
    {G : Type*} [Group G]
    {x y : G}
    {F : RFactor G}
    (C : RCColl p x y F.word F.multiplicity)
    (hF : F.Good p a b) :
    RightPrimeRefinement p a b x y F := by
  simpa only [RFactor.withoutConjugator_conjugate] using
    (C.withoutConjugatorRefinement hF).conjugate F.conjugator

end RCColl

namespace Trace

/-- The exponent-zero trace is the single basic Hall-pair commutator. -/
def exponentZero
    (p : ℕ)
    {G : Type*} [Group G]
    (x y : G) :
    Trace p x y 0 0 where
  factors := [RFactor.hallPair]
  eval_eq := by
    simp
  factors_good := by
    intro F hF
    rw [List.mem_singleton] at hF
    subst F
    exact RFactor.good_basic

end Trace

end PPColl

end Towers

/-!
## Former `HP` staging layer

These declarations used to live in the former `Towers.Group.HP` staging
module.  They belong with the aggregate Hall-Petresco construction and are
kept here so the full collector API is available from the primary module.
-/

open scoped commutatorElement

namespace Towers
namespace PPColl

namespace RCColl
namespace RPAggreg

/-!
### Conditional correlated normalizer decomposition

The aggregate API in `HallPetresco` deliberately stops before constructing a
global normalizer.  It exposes the pieces consumed by the conditional
normalizer interface below:

* an initial source value in the universal free group;
* a frontier with at most one correlated pending batch;
* strict measure descent for that pending batch;
* a terminal resolution carrying certified factors.

The abstract `CNormal` remains useful when a caller already has
frontiers for every recursive batch.  It does not assert that such frontiers
exist.  The constructive path later in this file is narrower: it asks for the
missing coefficient budget only on the concrete optional batch emitted by a
selected initial pass.
-/

/-- The resolution type required after recursively collecting one pending
universal batch. -/
abbrev UniversalPendingResolution
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ)
    (B : UPBatch p w n) :=
  KResolu p universalLeft universalRight w n B.eval

/-- The completed certified resolution of the universal source value. -/
abbrev UResolu
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ) :=
  KResolu p universalLeft universalRight w n
    (universalSourceValue p w n)

/-- The initial frontier type for the universal source value. -/
abbrev UniversalSourceFrontier
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ)
    (parentMeasure : ℕ) :=
  KFront p universalLeft universalRight w n
    (universalSourceValue p w n) parentMeasure

namespace UPBatch

/-- The common parent of a universal pending batch lies strictly below the
aggregate cutoff. -/
lemma measure_pos
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (B : UPBatch p w n) :
    0 < B.measure :=
  CPBatch.measure_pos B

/-- Read the exact universal free-group value represented by a pending
batch. -/
lemma eval_error_list
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (B : UPBatch p w n) :
    B.eval = errorListEval B.errors :=
  rfl

/-- Every error retained in a universal pending batch descends below the
batch's common parent measure. -/
lemma child_measure
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (B : UPBatch p w n)
    (E : PError p universalLeft universalRight (kernelCutoff p w n))
    (hE : E ∈ B.errors) :
    E.childMeasure < B.measure :=
  CPBatch.child_measure B E hE

end UPBatch

/--
A correlated normalizer contract.

The initial frontier handles the original universal source.  The recursive
frontier handles exactly one correlated pending batch.  A recursive frontier
is allowed to return another pending batch, but the imported
`KFront` contract forces its measure to decrease.
-/
structure CNormal
    (p : ℕ) [Fact p.Prime]
    (w : CWord HPAtom)
    (n : ℕ) where
  initial :
    UniversalSourceFrontier p w n (initialMeasure p w n)
  refine :
    ∀ B : UPBatch p w n,
      KFront p universalLeft universalRight w n
        B.eval B.measure

namespace CNormal

/-- Read the initial universal frontier from a correlated normalizer. -/
def initialFrontier
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    UniversalSourceFrontier p w n (initialMeasure p w n) :=
  N.initial

/-- Read the recursive frontier attached to one pending universal batch. -/
def pendingFrontier
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n)
    (B : UPBatch p w n) :
    KFront p universalLeft universalRight w n
      B.eval B.measure :=
  N.refine B

/-- The optional pending batch returned by the initial frontier has measure
strictly below the diagnostic initial measure. -/
lemma initia_pendi_measu
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n)
    (B : UPBatch p w n)
    (hB : N.initial.pending = some B) :
    B.measure < initialMeasure p w n :=
  N.initial.measure_lt B hB

/-- The optional pending batch returned by a recursive frontier has measure
strictly below the batch currently being collected. -/
lemma refine_pendi_measu
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n)
    (B C : UPBatch p w n)
    (hC : (N.refine B).pending = some C) :
    C.measure < B.measure :=
  (N.refine B).measure_lt C hC

/-- Resolve one pending batch by repeatedly invoking the recursive frontier.
Termination is exactly the strict pending-batch measure decrease stored in
`KFront`. -/
noncomputable def resolvePending
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    (B : UPBatch p w n) →
      UniversalPendingResolution p w n B
  | B =>
      (N.refine B).resolve
        (fun C _hC =>
          resolvePending N C)
termination_by
  B => B.measure
decreasing_by
  exact (N.refine B).measure_lt C _hC

/-- The recursively resolved pending batch evaluates to the original
correlated batch value. -/
lemma resolve_pending_eval
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n)
    (B : UPBatch p w n) :
    CFactor.listEval (N.resolvePending B).factors = B.eval :=
  (N.resolvePending B).eval_eq

/-- Resolving a pending batch yields a list of certified successor factors. -/
noncomputable def resolvepe_factors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n)
    (B : UPBatch p w n) :
    List (CFactor p universalLeft universalRight w n) :=
  (N.resolvePending B).factors

/-- The factor-list view of pending resolution retains its exact evaluation
identity. -/
lemma resolv_pendi_facto
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n)
    (B : UPBatch p w n) :
    CFactor.listEval (N.resolvepe_factors B) = B.eval :=
  N.resolve_pending_eval B

/-- Resolve the initial universal source frontier after recursively solving
its optional pending prefix. -/
noncomputable def resolve
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    UResolu p w n :=
  N.initial.resolve
    (fun B _hB =>
      N.resolvePending B)

/-- The completed normalizer resolution evaluates to the required universal
right-prime successor source. -/
lemma resolve_eval_eq
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    CFactor.listEval N.resolve.factors =
      universalSourceValue p w n :=
  N.resolve.eval_eq

/-- Expose the completed certified factor list produced by a normalizer. -/
noncomputable def factors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    List (CFactor p universalLeft universalRight w n) :=
  N.resolve.factors

/-- The exposed completed factor list evaluates to the universal source. -/
lemma eval_factors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    CFactor.listEval N.factors =
      universalSourceValue p w n :=
  N.resolve_eval_eq

/-- Every raw factor obtained from the completed normalizer list has the
coordinatewise successor certificate required by the kernel boundary. -/
lemma certif_raw_facto
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    ∀ E ∈ CFactor.rawFactors N.factors,
      NSCert p w n E :=
  CFactor.certif_raw_facto N.factors

end CNormal

namespace UResolu

/-- Forget the recursive normalizer bookkeeping and package the resulting
universal certified list as a `FAggreg`. -/
def toFAggreg
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (R : UResolu p w n) :
    FAggreg p w n where
  factors :=
    CFactor.rawFactors R.factors
  eval_eq := by
    rw [CFactor.raw_list_factors, R.eval_eq]
    rfl
  factors_certificate := by
    exact ⟨CFactor.certif_raw_facto R.factors⟩

/-- Packaging a universal resolution retains the exact raw factor list. -/
@[simp]
lemma aggregate_factors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (R : UResolu p w n) :
    R.toFAggreg.factors =
      CFactor.rawFactors R.factors :=
  rfl

/-- Packaging a universal resolution retains its universal evaluation
identity. -/
lemma free_aggre_facto
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (R : UResolu p w n) :
    listEval universalLeft universalRight R.toFAggreg.factors =
      universalSourceValue p w n := by
  rw [R.toFAggreg.eval_eq]
  rfl

/-- Packaging a universal resolution retains each coordinatewise factor
certificate. -/
lemma free_aggre_certi
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (R : UResolu p w n)
    {E : RFactor UniversalGroup}
    (hE : E ∈ R.toFAggreg.factors) :
    NSCert p w n E :=
  R.toFAggreg.factor_certificate hE

end UResolu

namespace CNormal

/-- Run a correlated normalizer and forget its recursive bookkeeping. -/
noncomputable def toFAggreg
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    FAggreg p w n :=
  N.resolve.toFAggreg

/-- The aggregate produced by a normalizer is backed by the normalizer's
completed certified factor list. -/
@[simp]
lemma aggregate_factors
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    N.toFAggreg.factors =
      CFactor.rawFactors N.factors :=
  rfl

/-- The aggregate produced by a normalizer has the required universal source
evaluation. -/
lemma free_aggregate_eval
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n) :
    listEval universalLeft universalRight N.toFAggreg.factors =
      universalSourceValue p w n :=
  N.resolve.free_aggre_facto

/-- The aggregate produced by a normalizer retains the factor certificate
for every member of its raw factor list. -/
lemma free_aggre_certi
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (N : CNormal p w n)
    {E : RFactor UniversalGroup}
    (hE : E ∈ N.toFAggreg.factors) :
    NSCert p w n E :=
  N.toFAggreg.factor_certificate hE

end CNormal

/-!
### Staged construction of the initial frontier

The first aggregate frontier has two logically separate jobs.

* A Hall traversal must expose an ordered raw suffix and, if necessary, one
  correlated pending prefix while preserving the exact free-group product.
* Every raw suffix member must receive the coordinatewise successor
  certificate required at the kernel boundary.

Keeping those jobs separate matters.  The raw Hall traversal is about
noncommutative collection order.  The suffix certification is pointwise
arithmetic.  Neither task alone constructs a `KFront`, and the
measure field of the final frontier is discharged independently from the
diagnostic initial measure.
-/

namespace CFactor

/-- Attach one already-proved successor certificate to a raw factor. -/
def ofRaw
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    {w : CWord HPAtom}
    {n : ℕ}
    (E : RFactor G)
    (hE : NSCert p w n E) :
    CFactor p x y w n where
  factor := E
  certificate := hE

/-- Attach pointwise successor certificates to an ordered raw factor list.

This conversion does not reorder, normalize, or re-evaluate the list.  It is
the bookkeeping bridge between a raw Hall traversal and the certified suffix
stored by `KFront`. -/
def listOfRaw
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    {w : CWord HPAtom}
    {n : ℕ} :
    (L : List (RFactor G)) →
      (∀ E ∈ L, NSCert p w n E) →
        List (CFactor p x y w n)
  | [], _hL =>
      []
  | E :: L, hL =>
      ofRaw x y E (hL E (by simp)) ::
        listOfRaw x y L (fun D hD => hL D (by simp [hD]))

/-- The raw factor underlying `ofRaw` is the supplied factor. -/
@[simp]
lemma factor_ofRaw
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    {w : CWord HPAtom}
    {n : ℕ}
    (E : RFactor G)
    (hE : NSCert p w n E) :
    (ofRaw x y E hE).factor = E :=
  rfl

/-- Certifying the empty raw list produces the empty certified list. -/
@[simp]
lemma list_raw_nil
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    {w : CWord HPAtom}
    {n : ℕ}
    (hL :
      ∀ E ∈ ([] : List (RFactor G)),
        NSCert p w n E) :
    listOfRaw x y [] hL = [] :=
  rfl

/-- Certifying a raw cons retains the head and recursively certifies the tail. -/
lemma list_raw_cons
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    {w : CWord HPAtom}
    {n : ℕ}
    (E : RFactor G)
    (L : List (RFactor G))
    (hL :
      ∀ D ∈ E :: L,
        NSCert p w n D) :
    listOfRaw x y (E :: L) hL =
      ofRaw x y E (hL E (by simp)) ::
        listOfRaw x y L (fun D hD => hL D (by simp [hD])) :=
  rfl

/-- Forgetting certificates after `listOfRaw` returns the original raw list. -/
@[simp]
lemma raw_factors_list
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    {w : CWord HPAtom}
    {n : ℕ}
    (L : List (RFactor G))
    (hL :
      ∀ E ∈ L,
        NSCert p w n E) :
    rawFactors (listOfRaw x y L hL) = L := by
  induction L with
  | nil =>
      rfl
  | cons E L ih =>
      change
        E ::
            rawFactors
              (listOfRaw x y L
                (fun D hD => hL D (by simp [hD]))) =
          E :: L
      congr
      exact ih _

/-- Attaching certificates leaves the ordered group evaluation unchanged. -/
lemma list_eval_raw
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    {w : CWord HPAtom}
    {n : ℕ}
    (L : List (RFactor G))
    (hL :
      ∀ E ∈ L,
        NSCert p w n E) :
    listEval (listOfRaw x y L hL) =
      PPColl.listEval x y L := by
  rw [← raw_list_factors, raw_factors_list]

/-- Every member of the certified list produced by `listOfRaw` still carries
its pointwise successor certificate. -/
lemma certificate_list_raw
    {p : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    {w : CWord HPAtom}
    {n : ℕ}
    (L : List (RFactor G))
    (hL :
      ∀ E ∈ L,
        NSCert p w n E)
    (F : CFactor p x y w n)
    (_hF : F ∈ listOfRaw x y L hL) :
    NSCert p w n F.factor :=
  F.certificate

end CFactor

namespace UPTask

/-- Decorate the exact ordered raw view of a budget-bearing task. -/
def admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : UPTask p w n) :
    List (CFactor p universalLeft universalRight w n) :=
  CFactor.listOfRaw
    universalLeft universalRight T.batch.rawFactors
      T.budget.certif_raw_facto

/-- Forgetting the task's decorations recovers its exact raw-factor view. -/
@[simp]
lemma rawFactors_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : UPTask p w n) :
    CFactor.rawFactors T.admitted =
      T.batch.rawFactors := by
  simp [admitted]

/-- Decorating a budget-bearing task leaves its ordered evaluation
unchanged. -/
lemma listEval_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : UPTask p w n) :
    CFactor.listEval T.admitted =
      T.batch.eval := by
  unfold admitted
  rw [CFactor.list_eval_raw]
  exact T.batch.list_raw_factors

/-- A budget-bearing pending task is already a terminal kernel frontier.

This is the sound replacement for recursively refining an arbitrary
diagnostic batch. -/
def toKFront
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : UPTask p w n) :
    KFront p universalLeft universalRight w n
      T.batch.eval T.batch.measure where
  pending :=
    none
  admitted :=
    T.admitted
  eval_eq := by
    simp [pendingEval, T.listEval_admitted]
  pending_decrease := by
    simp

/-- The task frontier is terminal by construction. -/
@[simp]
lemma kernel_front_pendi
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : UPTask p w n) :
    T.toKFront.pending = none :=
  rfl

/-- Read the decorated factors stored by the task frontier. -/
@[simp]
lemma kernel_front_admit
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : UPTask p w n) :
    T.toKFront.admitted = T.admitted :=
  rfl

/-- Resolve a budget-bearing task without inventing another pending batch. -/
def resolution
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : UPTask p w n) :
    UniversalPendingResolution p w n T.batch :=
  T.toKFront.resolve (fun B hB => by simp at hB)

/-- The terminal task resolution evaluates to the original diagnostic batch
value. -/
lemma resolution_eval_eq
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (T : UPTask p w n) :
    CFactor.listEval T.resolution.factors =
      T.batch.eval :=
  T.resolution.eval_eq

end UPTask

namespace URPass

/-- Evaluate the optional correlated pending prefix of a raw first pass. -/
def pendingValue
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n) :
    UniversalGroup :=
  pendingEval P.pending

/-- Evaluate the ordered admitted suffix of a raw first pass. -/
def admittedValue
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n) :
    UniversalGroup :=
  PPColl.listEval
    universalLeft universalRight P.admitted

/-- The raw first-pass identity expressed through its named prefix and suffix
views. -/
lemma pending_value_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n) :
    P.pendingValue * P.admittedValue =
      universalSourceValue p w n :=
  P.eval_eq

/-- Read one pointwise certificate from a certified raw suffix. -/
lemma certificate_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.SuffixCertified)
    (E : RFactor UniversalGroup)
    (hE : E ∈ P.admitted) :
    NSCert p w n E :=
  hP E hE

/-- Read the budget attached to the concrete pending batch returned by a
certified pass. -/
lemma budget_pending_some
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.PendingCertified)
    (B : UPBatch p w n)
    (hB : P.pending = some B) :
    UPBudget w n B :=
  hP B hB

/-- Any pending batch lies at or below the numerical kernel cutoff. -/
lemma batch_measure_cutoff
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (B : UPBatch p w n) :
    B.measure ≤ kernelCutoff p w n := by
  change
    kernelCutoff p w n -
        (B.left.weight (weight p) + B.right.weight (weight p)) ≤
      kernelCutoff p w n
  exact Nat.sub_le _ _

/-- Every possible pending result of an initial pass decreases below the
diagnostic initial measure.  This part of the frontier construction is
numeric; it does not require another Hall traversal. -/
lemma pendin_measu_initi
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (B : UPBatch p w n)
    (_hB : P.pending = some B) :
    B.measure < initialMeasure p w n := by
  rw [initialMeasure]
  exact Nat.lt_succ_of_le (batch_measure_cutoff B)

/-- Decorate the admitted raw suffix without changing its order. -/
def certifiedAdmitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.SuffixCertified) :
    List (CFactor p universalLeft universalRight w n) :=
  CFactor.listOfRaw
    universalLeft universalRight P.admitted hP

/-- Forgetting the decorations on a certified first-pass suffix recovers the
raw suffix exactly. -/
@[simp]
lemma raw_certified_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.SuffixCertified) :
    CFactor.rawFactors (P.certifiedAdmitted hP) =
      P.admitted := by
  simp [certifiedAdmitted]

/-- Decorating a first-pass suffix preserves its universal free-group
evaluation. -/
lemma list_certi_admit
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.SuffixCertified) :
    CFactor.listEval (P.certifiedAdmitted hP) =
      PPColl.listEval
        universalLeft universalRight P.admitted := by
  exact
    CFactor.list_eval_raw
      universalLeft universalRight P.admitted hP

/-- Assemble a kernel frontier after the two independent first-pass stages
have been supplied. -/
def toKFront
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.SuffixCertified) :
    UniversalSourceFrontier p w n (initialMeasure p w n) where
  pending :=
    P.pending
  admitted :=
    P.certifiedAdmitted hP
  eval_eq := by
    rw [P.list_certi_admit hP]
    exact P.eval_eq
  pending_decrease :=
    P.pendin_measu_initi

/-- The assembled frontier retains the pending correlated prefix exactly. -/
@[simp]
lemma kernel_front_pendi
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.SuffixCertified) :
    (P.toKFront hP).pending = P.pending :=
  rfl

/-- The assembled frontier uses the decorated view of the raw admitted
suffix. -/
@[simp]
lemma kernel_front_admit
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.SuffixCertified) :
    (P.toKFront hP).admitted =
      P.certifiedAdmitted hP :=
  rfl

/-- Forgetting the assembled frontier's admitted certificates recovers the
raw traversal suffix exactly. -/
@[simp]
lemma raw_frontier_admitted
    {p : ℕ} [Fact p.Prime]
    {w : CWord HPAtom}
    {n : ℕ}
    (P : URPass p w n)
    (hP : P.SuffixCertified) :
    CFactor.rawFactors (P.toKFront hP).admitted =
      P.admitted := by
  simp

end URPass

/--
Construct a terminal frontier from one budget-bearing pending task.

The task carries the coefficient evidence omitted by
`CPBatch`.  Consequently this theorem is constructive and
does not assert that arbitrary geometric diagnostics can be recursively
normalized.
-/
lemma nonempty_pass_provider
    {p : ℕ} [Fact p.Prime]
    (_provider : OrbitPassProvider p universalLeft universalRight)
    (w : CWord HPAtom)
    (_hw : w.PBPos)
    (n : ℕ)
    (T : UPTask p w n) :
    Nonempty
      (KFront p universalLeft universalRight w n
        T.batch.eval T.batch.measure) := by
  exact ⟨T.toKFront⟩

end RPAggreg
end RCColl
end PPColl
end Towers
