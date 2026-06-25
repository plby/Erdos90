import Submission.Group.Zassenhaus.CollectionBoundThree
import Submission.Group.Zassenhaus.BoundConcreteHall
import Submission.Group.Zassenhaus.HallCoordinateDn
import Submission.Group.Zassenhaus.FinitePGroup
import Submission.Group.Zassenhaus.FamilyScheduledBatch

/-!
# Paper-facing collection bounds for `docs/c.tex`

This module gives stable `Ctex` names to the final Hall--Zassenhaus collection
bound proved by the free lower-central truncation machinery.
-/

namespace Submission
namespace Ctex

universe u

open TCTex
open CCThree
open UWSkelet
open CRLayer
open RPCrit
open AMCrit
open ISFiber
open RHSplit
open RFTransv
open TFIdx
open SICollec


/--
The exponent `α(r)` from `docs/c.tex`: the least exponent whose weighted
prime power reaches the Zassenhaus level `n`.
-/
noncomputable def normalizedZassenhausExponent
    (p n r : ℕ) [Fact p.Prime] : ℕ :=
  leastWeightedExponent p n r

/--
The exponent `α(r)` reaches the requested Zassenhaus level.
-/
theorem normalized_exponent_spec
    (p n r : ℕ) [Fact p.Prime]
    (hr : 1 ≤ r) :
    n ≤ r * p ^ normalizedZassenhausExponent p n r := by
  exact mul_least_exponent p n r hr

/--
Minimality of `α(r)`: every smaller exponent fails to reach level `n`.
-/
theorem weighted_normalized_exponent
    (p n r a : ℕ) [Fact p.Prime]
    (hr : 1 ≤ r)
    (ha : a < normalizedZassenhausExponent p n r) :
    r * p ^ a < n := by
  exact Nat.lt_of_not_ge fun hlevel =>
    not_le_of_gt ha
      (least_prime_exponent (p := p) (n := n) (s := r)
        (j := a) hr hlevel)

/--
Combined minimum-exponent characterization of the paper's `α(r)`.
-/
theorem normalized_exponent_characterization
    (p n r : ℕ) [Fact p.Prime]
    (hr : 1 ≤ r) :
    n ≤ r * p ^ normalizedZassenhausExponent p n r ∧
      ∀ a : ℕ,
        a < normalizedZassenhausExponent p n r →
          r * p ^ a < n :=
  ⟨normalized_exponent_spec p n r hr,
    fun a ha =>
      weighted_normalized_exponent
        p n r a hr ha⟩

/--
The normalized Hall word-form attached to one Hall commutator, corresponding
to `W_i = \widetilde h_i^{p^{α_i}}` in `docs/c.tex`.
-/
noncomputable def normalizedWordScheme
    {p d n r : ℕ} [Fact p.Prime]
    (h : BCWt.{u} d r)
    (hr : 1 ≤ r) :
    ZWScheme p n :=
  h.freshenleast_weightprime_powerscheme (p := p) (n := n) hr

/-- The normalized Hall word has one formal input for each labelled leaf. -/
theorem normalized_scheme_arity
    {p d n r : ℕ} [Fact p.Prime]
    (h : BCWt.{u} d r)
    (hr : 1 ≤ r) :
    (normalizedWordScheme (p := p) (n := n) h hr).arity =
      h.word.weight (fun _ => 1) := by
  rfl

/-- The Frobenius exponent of the normalized Hall word is the paper's `α(r)`. -/
theorem normalized_scheme_frobenius
    {p d n r : ℕ} [Fact p.Prime]
    (h : BCWt.{u} d r)
    (hr : 1 ≤ r) :
    (normalizedWordScheme (p := p) (n := n) h hr).frobenius =
      normalizedZassenhausExponent p n r := by
  rfl

/-- Evaluation of a normalized Hall word is a `p^α`-power of its freshened commutator word. -/
theorem normalized_scheme_pow
    {p d n r : ℕ} [Fact p.Prime]
    (h : BCWt.{u} d r)
    (hr : 1 ≤ r)
    {G : Type u} [Group G]
    (a : Fin (normalizedWordScheme (p := p) (n := n) h hr).arity → G) :
    (normalizedWordScheme (p := p) (n := n) h hr).eval a =
      (normalizedWordScheme (p := p) (n := n) h hr).word.eval a ^
        (p ^ normalizedZassenhausExponent p n r) := by
  rw [ZWScheme.eval_def,
    normalized_scheme_frobenius (p := p) (n := n) h hr]

/-- Every normalized Hall word-value lies in the requested Zassenhaus term. -/
theorem normalized_scheme_filtration
    {p d n r : ℕ} [Fact p.Prime]
    (h : BCWt.{u} d r)
    (hr : 1 ≤ r)
    {G : Type u} [Group G]
    (a : Fin (normalizedWordScheme (p := p) (n := n) h hr).arity → G) :
    (normalizedWordScheme (p := p) (n := n) h hr).eval a ∈
      zassenhausFiltration p G n :=
  (normalizedWordScheme (p := p) (n := n) h hr).eval_zassenhaus_filtration a

/--
Paper-facing package for Hall's collection-polynomial/Petresco input on the
concrete Hall basis.  These are the three polynomial data families consumed
by the Hall-coordinate proof of the c.tex theorem.
-/
structure HallCollectionInputs (d n : ℕ) where
  power :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d)) (t : ℕ),
      1 ≤ t →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e t
  product :
    ∀ e :
        List
          (HEFam
            (concreteCommutatorsWeight.{u} d)),
      CollectedCoordinateData
        (n := n) (concreteCommutatorsWeight.{u} d) e
  inverse :
    ∀ e :
        HEFam
          (concreteCommutatorsWeight.{u} d),
      CollectedInverseData
        (n := n) (concreteCommutatorsWeight.{u} d) e

/--
Concrete c.tex form of the labelled Hall-commutator leading-coordinate lemma.
Freshening a Hall commutator and powering one labelled leaf by `m` gives the
selected Hall coordinate `m`, no other coordinate in the same ordinary weight,
and no lower-weight coordinates.
-/
theorem labelled_leading_coordinate
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (concreteCommutatorsWeight.{u} d r).index)
    (m : ℤ) :
    ∃ a : Fin (((concreteCommutatorsWeight.{u} d r).commutator i).word.weight
          (fun _ => 1)) →
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
      let y :=
        (CWord.freshen
          ((concreteCommutatorsWeight.{u} d r).commutator i).word).eval a
      (∀ s : ℕ,
        1 ≤ s →
          s < r →
            s < n →
              ∀ j : (concreteCommutatorsWeight.{u} d s).index,
                hallCoordinate hn (concreteCommutatorsWeight.{u} d)
                    (fun t ht htn =>
                      concrete_forms_associated
                        d n t ht htn)
                    y j =
                  0) ∧
        ∀ j : (concreteCommutatorsWeight.{u} d r).index,
          hallCoordinate hn (concreteCommutatorsWeight.{u} d)
              (fun t ht htn =>
                concrete_forms_associated
                  d n t ht htn)
              y j =
            if j = i then m else 0 :=
  TCTex.labelled_leading_coordinate
    hn (concreteCommutatorsWeight.{u} d)
    (fun s hs hsn =>
      concrete_forms_associated d n s hs hsn)
    hr hrn i m

/--
Concrete c.tex form of the normalized leading-coordinate lemma.  The
normalized Hall word-value has selected coordinate `p^alpha * m`, no lower
coordinates, and lies in the requested Zassenhaus term.
-/
theorem normalized_leading_coordinate
    {p d n r : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (concreteCommutatorsWeight.{u} d r).index)
    (m : ℤ) :
    ∃ a : Fin (((concreteCommutatorsWeight.{u} d r).commutator i).word.weight
          (fun _ => 1)) →
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
      let S :=
        ((concreteCommutatorsWeight.{u} d r).commutator i).freshenleast_weightprime_powerscheme
          (p := p) (n := n) hr
      let y := S.eval a
      (∀ s : ℕ,
        1 ≤ s →
          s < r →
            s < n →
              ∀ j : (concreteCommutatorsWeight.{u} d s).index,
                hallCoordinate hn (concreteCommutatorsWeight.{u} d)
                    (fun t ht htn =>
                      concrete_forms_associated
                        d n t ht htn)
                    y j =
                  0) ∧
        (∀ j : (concreteCommutatorsWeight.{u} d r).index,
          hallCoordinate hn (concreteCommutatorsWeight.{u} d)
              (fun t ht htn =>
                concrete_forms_associated
                  d n t ht htn)
              y j =
            if j = i then
              ((p ^ normalizedZassenhausExponent p n r : ℕ) : ℤ) * m
            else 0) ∧
        y ∈ zassenhausFiltration
          p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n :=
  by
    simpa [normalizedZassenhausExponent] using
      TCTex.normalized_leading_coordinate
        (p := p) hn (concreteCommutatorsWeight.{u} d)
        (fun s hs hsn =>
          concrete_forms_associated d n s hs hsn)
        hr hrn i m

/--
Concrete Hall-coordinate description of `D_n(F_d / gamma_n(F_d))` from the
collection-polynomial inputs: membership in the Zassenhaus term is exactly
divisibility of every ordinary-weight Hall coordinate by the normalized
prime-power exponent attached to that weight.
-/
theorem filtration_concrete_dvd
    {p d n : ℕ}
    [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : HallCollectionInputs.{u} d n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n ↔
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            ∀ i : (concreteCommutatorsWeight.{u} d s).index,
              ((p ^ normalizedZassenhausExponent p n s : ℕ) : ℤ) ∣
                hallCoordinate hn (concreteCommutatorsWeight.{u} d)
                  (fun t ht htn =>
                    concrete_forms_associated
                      d n t ht htn)
                  y i := by
  simpa [normalizedZassenhausExponent] using
    TCTex.zassenhaus_filtration_dvd
      (p := p) (d := d) (n := n) hn
      (concreteCommutatorsWeight.{u} d)
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      I.power I.product I.inverse y

/--
The c.tex free-truncation collection bound from Hall collection-polynomial
inputs, with the explicit bound `M`.
-/
theorem uniform_bound_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : HallCollectionInputs.{u} d n) :
    TruncationCollectionBound.{u}
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) :=
  commutators_collect_poly (p := p) (d := d) (n := n)
    hn I.power I.product I.inverse

/--
Direct elementwise form of the c.tex theorem from Hall collection-polynomial
inputs.
-/
theorem uniform_zassenhaus_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : HallCollectionInputs.{u} d n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n) :
    BNZass
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) y :=
  uniform_bound_inputs
    (p := p) (d := d) (n := n) hn I y hy

/-- Existential form of the Hall collection-polynomial-input bound. -/
theorem uniform_bounded_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : HallCollectionInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow
      (concreteCommutatorsWeight.{u} d) n,
    uniform_bound_inputs
      hn I⟩

/--
The arbitrary-cutoff inputs currently used by the concrete Hall collection
pipeline: a retained recipe law, supported low-weight power sources, ranked
power builders, and a structural signed builder.
-/
structure RCInputs (d n : ℕ) where
  retainedRecipeLaw :
    SatisfiesRecipeCoefficient.{u} d n
  lowWeightSource :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        ¬n ≤ 3 * inputWeight →
          TSInput
            (n := n) (inputWeight := inputWeight)
              (concreteCommutatorsWeight.{u} d) e
  lowWeightSupported :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ)
      (hinputWeight : 1 ≤ inputWeight)
      (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
        SPFactora.WordWeightLeast inputWeight
          (lowWeightSource e inputWeight hinputWeight
            hbelowClassTwoRange).source
  powerBuilders :
    ∀ inputWeight : ℕ,
      1 ≤ inputWeight →
        TCBuildb.{u}
          (d := d) (n := n) (inputWeight := inputWeight)
  signedBuilder :
    TBBuild.{u} (d := d) (n := n)

/--
Paper-facing package for the strongest generated arbitrary-cutoff boundary:
one universal signed-block assignment, low-weight Hall-power sources, and the
two singleton-normalization callbacks needed by the powered and signed
recollection pipelines.
-/
structure UniversalCollectionInputs (d n : ℕ) where
  leftWeight : ℕ
  rightWeight : ℕ
  leftWeight_pos : 0 < leftWeight
  rightWeight_pos : 0 < rightWeight
  lowWeightSource :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        ¬n ≤ 3 * inputWeight →
          TSInput
            (n := n) (inputWeight := inputWeight)
              (concreteCommutatorsWeight.{u} d) e
  lowWeightSupported :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ)
      (hinputWeight : 1 ≤ inputWeight)
      (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
        SPFactora.WordWeightLeast inputWeight
          (lowWeightSource e inputWeight hinputWeight
            hbelowClassTwoRange).source
  assignment :
    UPAssign.{u}
      n leftWeight rightWeight leftWeight_pos rightWeight_pos
  powerFactorNormalization :
    ∀ (inputWeight : ℕ),
      1 ≤ inputWeight →
        ∀ lowerWeight : ℕ,
          ¬n ≤ 2 * lowerWeight →
            TSNormalb
                (n := n) (inputWeight := inputWeight)
                  (lowerWeight := lowerWeight + 1)
                    (concreteCommutatorsWeight.{u} d) →
              ∀ (factor :
                  SPFactora
                    (concreteCommutatorsWeight.{u} d)
                      inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TANorm
                      (n := n) (lowerWeight := lowerWeight)
                        (concreteCommutatorsWeight.{u} d) factor
  signedFactorNormalization :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1)
              (concreteCommutatorsWeight.{u} d) →
          ∀ (factor :
              SPFactor
                (concreteCommutatorsWeight.{u} d) ι),
            factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPActive
                  (n := n) (lowerWeight := lowerWeight)
                    (concreteCommutatorsWeight.{u} d) ι factor

/--
Finite-index trace/profile inputs for the strongest currently exposed
Hall-power route.  The raw-source finite-index profile and retained correction
profile provide the power-coordinate data; product and inverse data are kept
as explicit sibling inputs.
-/
structure ProfileCollectionInputs (d n : ℕ) where
  layer : NRLayer n 1 1
  raw :
    PTStab n 1 1
  corrections :
    SFProf
      layer (by simp) (by simp)
  listEval :
    EFSplit.SatisfiesTruncEval.{u}
      (d := d)
      (fiberProfileSplit
        (PTStab.idxFiberProfile
          raw (by simp) (by simp))
        corrections)
  lowWeightSource :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        ¬n ≤ 3 * inputWeight →
          TSInput
            (n := n) (inputWeight := inputWeight)
              (concreteCommutatorsWeight.{u} d) e
  lowWeightSupported :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ)
      (hinputWeight : 1 ≤ inputWeight)
      (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
        SPFactora.WordWeightLeast inputWeight
          (lowWeightSource e inputWeight hinputWeight
            hbelowClassTwoRange).source
  factorNormalization :
    ∀ inputWeight : ℕ,
      1 ≤ inputWeight →
        ∀ lowerWeight : ℕ,
          ¬n ≤ 2 * lowerWeight →
            TSNormalb
                (n := n) (inputWeight := inputWeight)
                  (lowerWeight := lowerWeight + 1)
                    (concreteCommutatorsWeight.{u} d) →
              ∀ (factor :
                  SPFactora
                    (concreteCommutatorsWeight.{u} d)
                      inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TANorm
                      (n := n) (lowerWeight := lowerWeight)
                        (concreteCommutatorsWeight.{u} d) factor
  product :
    ∀ e :
        List
          (HEFam
            (concreteCommutatorsWeight.{u} d)),
      CollectedCoordinateData
        (n := n) (concreteCommutatorsWeight.{u} d) e
  inverse :
    ∀ e :
        HEFam
          (concreteCommutatorsWeight.{u} d),
      CollectedInverseData
        (n := n) (concreteCommutatorsWeight.{u} d) e

/--
Finite-index trace/profile inputs give the free-truncation collection bound.
-/
theorem uniform_collection_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : ProfileCollectionInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  TCTex.free_fiber_profiles
    p d n hn
    (layer := I.layer)
    I.raw I.corrections I.listEval
    I.lowWeightSource I.lowWeightSupported
    I.factorNormalization I.product I.inverse

/--
Finite-group collection consequence of the finite-index trace/profile inputs.
-/
theorem collection_index_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : ProfileCollectionInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  collection_truncation_bound
    p d n hn
    (uniform_collection_inputs
      (p := p) (d := d) (n := n) hn I)

/--
Scalar finite-index raw-source trace counts produce the raw stabilization
kernel used by the finite-index trace/profile input package.
-/
noncomputable def stabilization_fiber_counts
    {n : ℕ}
    (counts :
      SatisfiesTransversalCounts
        n 1 1 (by simp) (by simp)) :
    PTStab n 1 1 :=
  (transversal_stabilization_counts
      (by simp : 0 < 1) (by simp : 0 < 1)).mpr counts

/--
Finite-index trace/profile inputs where the raw source profile is supplied in
the equivalent finite-index count form.
-/
structure SCInputs (d n : ℕ) where
  layer : NRLayer n 1 1
  counts :
    SatisfiesTransversalCounts
      n 1 1 (by simp) (by simp)
  corrections :
    SFProf
      layer (by simp) (by simp)
  listEval :
    EFSplit.SatisfiesTruncEval.{u}
      (d := d)
      (fiberProfileSplit
        (PTStab.idxFiberProfile
          (stabilization_fiber_counts
            counts)
          (by simp) (by simp))
        corrections)
  lowWeightSource :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        ¬n ≤ 3 * inputWeight →
          TSInput
            (n := n) (inputWeight := inputWeight)
              (concreteCommutatorsWeight.{u} d) e
  lowWeightSupported :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ)
      (hinputWeight : 1 ≤ inputWeight)
      (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
        SPFactora.WordWeightLeast inputWeight
          (lowWeightSource e inputWeight hinputWeight
            hbelowClassTwoRange).source
  factorNormalization :
    ∀ inputWeight : ℕ,
      1 ≤ inputWeight →
        ∀ lowerWeight : ℕ,
          ¬n ≤ 2 * lowerWeight →
            TSNormalb
                (n := n) (inputWeight := inputWeight)
                  (lowerWeight := lowerWeight + 1)
                    (concreteCommutatorsWeight.{u} d) →
              ∀ (factor :
                  SPFactora
                    (concreteCommutatorsWeight.{u} d)
                      inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TANorm
                      (n := n) (lowerWeight := lowerWeight)
                        (concreteCommutatorsWeight.{u} d) factor
  product :
    ∀ e :
        List
          (HEFam
            (concreteCommutatorsWeight.{u} d)),
      CollectedCoordinateData
        (n := n) (concreteCommutatorsWeight.{u} d) e
  inverse :
    ∀ e :
        HEFam
          (concreteCommutatorsWeight.{u} d),
      CollectedInverseData
        (n := n) (concreteCommutatorsWeight.{u} d) e

/-- Convert scalar finite-index count inputs to the raw-profile package. -/
noncomputable def SCInputs.fin_indextrace_profileinputs
    {d n : ℕ}
    (I : SCInputs.{u} d n) :
    ProfileCollectionInputs.{u} d n where
  layer := I.layer
  raw := stabilization_fiber_counts I.counts
  corrections := I.corrections
  listEval := I.listEval
  lowWeightSource := I.lowWeightSource
  lowWeightSupported := I.lowWeightSupported
  factorNormalization := I.factorNormalization
  product := I.product
  inverse := I.inverse

/--
Scalar finite-index count inputs give the free-truncation collection bound.
-/
theorem uniform_scalar_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : SCInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  uniform_collection_inputs
    (p := p) (d := d) (n := n) hn
    I.fin_indextrace_profileinputs

/--
Finite-group collection consequence of scalar finite-index count inputs.
-/
theorem scalar_count_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : SCInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  collection_index_inputs
    (p := p) (d := d) (n := n) hn
    I.fin_indextrace_profileinputs

/--
Decomposed scheduled finite-index multiplicity inputs.  This exposes the
current deepest canonical scheduler boundary: exact occurrence accounting is
reduced to the three-way scalar local-collection formula carried by
`SDAlign`, together with the signed list-evaluation lift consumed
by the Claim 5 power route.
-/
structure DecomposedSchedulerInputs (d n : ℕ) where
  layer : NRLayer n 1 1
  scheduler :
    GPPerm layer (by simp) (by simp)
  alignment :
    SDAlign (by simp) (by simp) scheduler.raw
  listEval :
    SDAlign.SatisfiesTruncEval.{u}
      (d := d) scheduler alignment
  lowWeightSource :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        ¬n ≤ 3 * inputWeight →
          TSInput
            (n := n) (inputWeight := inputWeight)
              (concreteCommutatorsWeight.{u} d) e
  lowWeightSupported :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ)
      (hinputWeight : 1 ≤ inputWeight)
      (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
        SPFactora.WordWeightLeast inputWeight
          (lowWeightSource e inputWeight hinputWeight
            hbelowClassTwoRange).source
  factorNormalization :
    ∀ inputWeight : ℕ,
      1 ≤ inputWeight →
        ∀ lowerWeight : ℕ,
          ¬n ≤ 2 * lowerWeight →
            TSNormalb
                (n := n) (inputWeight := inputWeight)
                  (lowerWeight := lowerWeight + 1)
                    (concreteCommutatorsWeight.{u} d) →
              ∀ (factor :
                  SPFactora
                    (concreteCommutatorsWeight.{u} d)
                      inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TANorm
                      (n := n) (lowerWeight := lowerWeight)
                        (concreteCommutatorsWeight.{u} d) factor
  product :
    ∀ e :
        List
          (HEFam
            (concreteCommutatorsWeight.{u} d)),
      CollectedCoordinateData
        (n := n) (concreteCommutatorsWeight.{u} d) e
  inverse :
    ∀ e :
        HEFam
          (concreteCommutatorsWeight.{u} d),
      CollectedInverseData
        (n := n) (concreteCommutatorsWeight.{u} d) e

/--
Decomposed scheduled multiplicity inputs give the free-truncation collection
bound.
-/
theorem uniform_decomposed_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : DecomposedSchedulerInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k := by
  apply
    TCTex.truncation_collection_data
      p d n hn
  · intro e inputWeight hinputWeight
    by_cases hclassTwoRange : n ≤ 3 * inputWeight
    · exact
        collected_semantic_below
          hn (concreteCommutatorsWeight.{u} d)
            (forms_associated_below
              d n)
            hinputWeight hclassTwoRange
    · exact
        TSInput.coordDecomposedTrunc
          hn (concreteCommutatorsWeight.{u} d)
            (forms_associated_below
              d n)
          I.scheduler I.alignment I.listEval
          (I.lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (I.lowWeightSupported e inputWeight hinputWeight
            hclassTwoRange)
          (I.factorNormalization inputWeight hinputWeight)
          hinputWeight
  · exact I.product
  · exact I.inverse

/--
Finite-group collection consequence of decomposed scheduled multiplicity
inputs.
-/
theorem collection_decomposed_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : DecomposedSchedulerInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  collection_truncation_bound
    p d n hn
    (uniform_decomposed_inputs
      (p := p) (d := d) (n := n) hn I)

/--
Arbitrary-cutoff free-truncation collection bound from a universal signed-block
Hall-Petresco package and the remaining local source/normalization callbacks.
-/
theorem uniform_universal_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : UniversalCollectionInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  TCTex.assignment_singleton_normalizations
    p d n I.leftWeight I.rightWeight hn I.leftWeight_pos
      I.rightWeight_pos I.lowWeightSource I.lowWeightSupported
      I.assignment I.powerFactorNormalization I.signedFactorNormalization

/--
Transport the arbitrary-cutoff free-truncation collection bound obtained from
universal signed-block inputs to every generated quotient modulo its
`γ_n`-term.
-/
theorem truncated_universal_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : UniversalCollectionInputs.{u} d n) :
    ∃ k : ℕ, TruncatedCollectionBound.{u} p d n k := by
  obtain ⟨k, hfree⟩ :=
    uniform_universal_inputs
      (p := p) (d := d) (n := n) hn I
  exact
    ⟨k,
      truncated_collection_truncation
        hfree⟩

/--
Finite-group collection consequence of the arbitrary-cutoff Ctex inputs.  This
uses the verified free-truncation bound from the inputs, the quotient transport
lemma, and the separate lower-central completion bound.
-/
theorem universal_block_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : UniversalCollectionInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) := by
  by_cases hd : d ≤ 1
  · exact
      Nonempty.map
        FSColl.toCollection
        (p_collection_generators
          (p := p) (d := d) (n := n) hd)
  have hdpos : 0 < d := by omega
  obtain ⟨kTrunc, hTrunc⟩ :=
    truncated_universal_inputs
      (p := p) (d := d) (n := n) hn I
  obtain ⟨kResidual, hResidual⟩ :=
    TCTex.lower_completion_bound
      p d n hdpos hn
  exact
    TCTex.te_x_leaves
      (kTrunc := kTrunc) (kResidual := kResidual)
      hTrunc hResidual

/--
Unconditional paper-facing free-truncation collection bound through nilpotence
class three, with the explicit c.tex bound `M`.
-/
theorem uniform_collection_four
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n) (hn4 : n ≤ 4) :
    TruncationCollectionBound.{u}
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) :=
  commutators_truncation_four
    hn hn4

/--
Direct elementwise form of the c.tex theorem through nilpotence class three:
every `y ∈ D_n(F_d / γ_n(F_d))` is a product of at most `M` normalized
Zassenhaus word-values.
-/
theorem uniform_bounded_four
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n) (hn4 : n ≤ 4)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n) :
    BNZass
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) y :=
  uniform_collection_four
    (p := p) (d := d) (n := n) hn hn4 y hy

/--
Existential form of the class-three paper-facing bound.
-/
theorem uniform_n_four
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n) (hn4 : n ≤ 4) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow
      (concreteCommutatorsWeight.{u} d) n,
    uniform_collection_four hn hn4⟩

/--
The powered retained-recipe builder supplies the singleton normalization
callback expected by the universal signed-block collection boundary.
-/
noncomputable def RCInputs.powerFactorNormalization
    {d n : ℕ}
    (hn : 2 ≤ n)
    (I : RCInputs.{u} d n) :
    ∀ (inputWeight : ℕ),
      1 ≤ inputWeight →
        ∀ lowerWeight : ℕ,
          ¬n ≤ 2 * lowerWeight →
            TSNormalb
                (n := n) (inputWeight := inputWeight)
                  (lowerWeight := lowerWeight + 1)
                    (concreteCommutatorsWeight.{u} d) →
              ∀ (factor :
                  SPFactora
                    (concreteCommutatorsWeight.{u} d)
                      inputWeight),
                factor.word.weight PEAddres.weight =
                    lowerWeight →
                  factor.word.weight PEAddres.weight < n →
                    TANorm
                      (n := n) (lowerWeight := lowerWeight)
                        (concreteCommutatorsWeight.{u} d) factor := by
  intro inputWeight hinputWeight lowerWeight _hactive _nextNormalizer
    factor hfactorWeight hfactorTruncated
  exact
    TANorm.ofNormalizer
      ((I.powerBuilders inputWeight hinputWeight)
        |>.semanticCoordinateNormalizer
          hn hinputWeight I.retainedRecipeLaw lowerWeight)
      factor
      (le_of_eq hfactorWeight.symm)
      hfactorTruncated

/--
The signed retained-recipe builder supplies the singleton normalization
callback expected by the universal signed-block collection boundary.
-/
noncomputable def RCInputs.signedFactorNormalization
    {d n : ℕ}
    (hn : 2 ≤ n)
    (I : RCInputs.{u} d n) :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1)
              (concreteCommutatorsWeight.{u} d) →
          ∀ (factor :
              SPFactor
                (concreteCommutatorsWeight.{u} d) ι),
            factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPActive
                  (n := n) (lowerWeight := lowerWeight)
                    (concreteCommutatorsWeight.{u} d) ι factor := by
  intro ι lowerWeight _hactive _nextNormalizer factor hfactorWeight
    hfactorTruncated
  exact
    TPActive.ofNormalizer
      (I.signedBuilder.supportedCoordinateNormalizer
        hn I.retainedRecipeLaw lowerWeight)
      factor
      (le_of_eq hfactorWeight.symm)
      hfactorTruncated

/--
Arbitrary-cutoff paper-facing free-truncation collection bound from the
retained-recipe inputs, again with the explicit c.tex bound `M`.
-/
theorem uniform_retained_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : RCInputs.{u} d n) :
    TruncationCollectionBound.{u}
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) := by
  apply commutators_collect_poly (p := p) (d := d) (n := n) hn
  · exact
      commutators_poly_builders
        hn I.retainedRecipeLaw I.lowWeightSource
          I.lowWeightSupported I.powerBuilders
  · intro e
    exact commutators_coeff_builder hn e I.signedBuilder I.retainedRecipeLaw
  · intro e
    exact commutators_supported_builder hn e I.signedBuilder I.retainedRecipeLaw

/--
Direct elementwise form of the arbitrary-cutoff c.tex theorem from the
retained-recipe inputs.
-/
theorem uniform_hall_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : RCInputs.{u} d n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ zassenhausFiltration
        p (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) n) :
    BNZass
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) y :=
  uniform_retained_inputs
    (p := p) (d := d) (n := n) hn I y hy

/-- Existential form of the retained-recipe-input collection bound. -/
theorem uniform_recipe_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : RCInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow
      (concreteCommutatorsWeight.{u} d) n,
    uniform_retained_inputs
      hn I⟩

/--
The retained-recipe Ctex inputs give the quotient-level collection bound with
the same explicit Hall-count bound `M`.
-/
theorem truncated_bound_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : RCInputs.{u} d n) :
    TruncatedCollectionBound.{u}
      p d n
        (commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n) :=
  truncated_collection_truncation
    (uniform_retained_inputs
      (p := p) (d := d) (n := n) hn I)

/-- Existential quotient-level form of the retained-recipe collection bound. -/
theorem truncated_collection_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : RCInputs.{u} d n) :
    ∃ k : ℕ, TruncatedCollectionBound.{u} p d n k :=
  ⟨commutatorCountBelow
      (concreteCommutatorsWeight.{u} d) n,
    truncated_bound_inputs
      hn I⟩

/--
Finite-group collection consequence of the retained-recipe Ctex inputs.  This
is a fully proved route through the free-truncation theorem, quotient transport,
and lower-central completion.
-/
theorem p_recipe_inputs
    {p d n : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : RCInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) := by
  by_cases hd : d ≤ 1
  · exact
      Nonempty.map
        FSColl.toCollection
        (p_collection_generators
          (p := p) (d := d) (n := n) hd)
  have hdpos : 0 < d := by omega
  obtain ⟨kResidual, hResidual⟩ :=
    TCTex.lower_completion_bound
      p d n hdpos hn
  exact
    TCTex.te_x_leaves
      (kTrunc :=
        commutatorCountBelow
          (concreteCommutatorsWeight.{u} d) n)
      (kResidual := kResidual)
      (truncated_bound_inputs
        (p := p) (d := d) (n := n) hn I)
      hResidual

end Ctex
end Submission
