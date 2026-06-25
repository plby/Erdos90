import Towers.Group.Zassenhaus.ClassTwoCollection
import Towers.Group.Zassenhaus.ConcretePackets
import Towers.Group.Zassenhaus.RewriteContexts
import Towers.Group.Zassenhaus.RewriteSupport
import Towers.Group.Zassenhaus.IntegerScaling

-- Merged from ClassTwoSources.lean

/-!
# Symbolic class-two powered Hall sources

When `n ≤ 3 * inputWeight`, powering an ordered Hall block has an explicit
finite symbolic source.  Each original Hall atom contributes a `choose q 1`
factor.  For every ordered pair of distinct positions, the later atom crossing
the earlier atom contributes their commutator with multiplicity `choose q 2`.

These factors are still commutator words rather than normalized atomic Hall
coordinates.  A general Hall scheduler must recollect them, but the genuinely
powered source identity is now finite and explicit throughout the class-two
region.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/-- One nonzero-eligible Hall atom in the input collected block. -/
structure SSAtom
    {d : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (inputWeight : ℕ) where
  address :
    HEAddres H
  coefficient :
    ℤ
  inputWeight_le :
    inputWeight ≤ PEAddres.weight address

namespace SSAtom

/-- The raw `choose q 1` symbolic factor attached to one source atom. -/
def factor
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atom : SSAtom H inputWeight) :
    SPFactora H inputWeight :=
  SPFactora.source atom.coefficient atom.address atom.inputWeight_le

/-- The unpowered group value represented by one source atom. -/
def value
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atom : SSAtom H inputWeight) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  PEAddres.freeLowerTruncation atom.address ^
    atom.coefficient

/-- Raw source factors evaluate to powers of their unpowered atom value. -/
@[simp] lemma eval_factor
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atom : SSAtom H inputWeight)
    (q : ℕ) :
    atom.factor.eval (n := n) q = atom.value ^ q := by
  rw [factor, SPFactora.eval_source]
  simp only [value, PEAddres.freeLowerTruncation,
    ← zpow_natCast, ← zpow_mul]

/-- Every source atom value lies in the initial lower-central term. -/
lemma value_initial_series
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atom : SSAtom H inputWeight) :
    atom.value (n := n) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inputWeight - 1) := by
  apply
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (inputWeight - 1)).zpow_mem
  exact Subgroup.lowerCentralSeries_antitone
    (Nat.sub_le_sub_right atom.inputWeight_le 1)
    (PEAddres.free_truncation_series
      atom.address)

/--
The `choose q 2` correction emitted when a later atom crosses an earlier atom
among repeated ordered blocks.
-/
def pairCorrection
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (later earlier : SSAtom H inputWeight) :
    SPFactora H inputWeight where
  word := .commutator (.atom later.address) (.atom earlier.address)
  coefficient := later.coefficient * earlier.coefficient
  recipe :=
    BBRecipe.select inputWeight
      (PEAddres.weight later.address +
        PEAddres.weight earlier.address)
      2 (by omega) (by
        have hlater := later.inputWeight_le
        have hearlier := earlier.inputWeight_le
        omega)

/-- Pair corrections have the sum of their two source weights. -/
@[simp] lemma word_pair_correction
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (later earlier : SSAtom H inputWeight) :
    (later.pairCorrection earlier).word.weight PEAddres.weight =
      PEAddres.weight later.address +
        PEAddres.weight earlier.address :=
  rfl

/--
In the class-two region, the symbolic pair correction evaluates to the
expected `choose q 2` power of the commutator of the unpowered source atoms.
-/
lemma eval_pairCorrection
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (q : ℕ) :
    (later.pairCorrection earlier).eval (n := n) q =
      ⁅later.value (n := n), earlier.value (n := n)⁆ ^ Nat.choose q 2 := by
  have hleft :
      n ≤
        2 * later.factor.word.weight PEAddres.weight +
          earlier.factor.word.weight PEAddres.weight := by
    simpa [factor, SPFactora.source] using
      (show n ≤
          2 * PEAddres.weight later.address +
            PEAddres.weight earlier.address by
        have hlater := later.inputWeight_le
        have hearlier := earlier.inputWeight_le
        omega)
  have hright :
      n ≤
        later.factor.word.weight PEAddres.weight +
          2 * earlier.factor.word.weight PEAddres.weight := by
    simpa [factor, SPFactora.source] using
      (show n ≤
          PEAddres.weight later.address +
            2 * PEAddres.weight earlier.address by
        have hlater := later.inputWeight_le
        have hearlier := earlier.inputWeight_le
        omega)
  have hbracket :
      (later.factor.bracket earlier.factor).eval (n := n) 1 =
        ⁅later.value (n := n), earlier.value (n := n)⁆ := by
    let hpacket :=
      SHPkt.singleton_bracket_two
        (n := n) later.factor earlier.factor hleft hright
    simpa [SPFactora.listEval, hpacket,
      SHPkt.singleton_bracket_two,
      SHPkt.bracket_commute,
      SHPkt.singletonBracket] using
        hpacket.listEval_eq 1
  calc
    (later.pairCorrection earlier).eval (n := n) q =
        ⁅PEAddres.freeLowerTruncation
            (n := n) later.address,
          PEAddres.freeLowerTruncation
            (n := n) earlier.address⁆ ^
          ((later.coefficient * earlier.coefficient) *
            (Nat.choose q 2 : ℤ)) := by
            simp [pairCorrection, SPFactora.eval,
              SPFactora.wordValue, SPFactora.exponent,
              BBRecipe.eval, BBRecipe.select,
              PBRecipe.select, PBRecipe.eval]
    _ = (later.factor.bracket earlier.factor).eval (n := n) 1 ^
          Nat.choose q 2 := by
            simp [factor, SPFactora.eval_bracket,
              PEAddres.freeLowerTruncation,
              ← zpow_natCast, ← zpow_mul]
    _ = ⁅later.value (n := n), earlier.value (n := n)⁆ ^ Nat.choose q 2 := by
      rw [hbracket]

/-- Pair corrections emitted against one fixed earlier head atom. -/
def pairCorrections
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (earlier : SSAtom H inputWeight)
    (later : List (SSAtom H inputWeight)) :
    List (SPFactora H inputWeight) :=
  later.reverse.map fun atom => atom.pairCorrection earlier

/--
The complete symbolic class-two powered source for one ordered atom list.
-/
def factors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    List (SSAtom H inputWeight) →
      List (SPFactora H inputWeight)
  | [] => []
  | atom :: atoms =>
      pairCorrections atom atoms ++ [atom.factor] ++ factors atoms

/-- Symbolic class-two factors match the value-level finite collector. -/
lemma list_factors_prod
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (q : ℕ) :
    ∀ atoms : List (SSAtom H inputWeight),
      SPFactora.listEval (n := n) q (factors atoms) =
        (cTFactor q (atoms.map fun atom => atom.value (n := n))).prod := by
  intro atoms
  induction atoms with
  | nil =>
      simp [factors, cTFactor]
  | cons atom atoms ih =>
      simp only [factors, SPFactora.listEval_append,
        SPFactora.listEval_cons,
        SPFactora.listEval_nil, mul_one, ih,
        cTFactor, List.map_cons, List.prod_append]
      simp [pairCorrections, SPFactora.listEval,
        eval_pairCorrection hcutoff, List.map_reverse, List.map_map,
        Function.comp_def]

/-- The symbolic class-two powered source evaluates to the power of its atom block. -/
lemma listEval_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (q : ℕ)
    (atoms : List (SSAtom H inputWeight)) :
    SPFactora.listEval (n := n) q (factors atoms) =
      (atoms.map fun atom => atom.value (n := n)).prod ^ q := by
  rw [list_factors_prod hcutoff]
  exact
    class_initial_series
      hinputWeight hcutoff q
      (atoms.map fun atom => atom.value (n := n)) (by
        intro x hx
        rcases List.mem_map.mp hx with ⟨atom, _hatom, rfl⟩
        exact atom.value_initial_series)

end SSAtom

/-- Eligible source atoms in one fixed Hall-weight layer. -/
noncomputable def collectedSourceAtoms
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (s : ℕ) :
    List (SSAtom H inputWeight) :=
  if hs : inputWeight ≤ s then
    (Finset.univ.sort fun i i' : (H s).index => i ≤ i').map fun i =>
      { address := ⟨s, i⟩
        coefficient := e s i
        inputWeight_le := hs }
  else
    []

/-- The values of one eligible source layer multiply to its collected Hall segment. -/
lemma value_collected_atoms
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (s : ℕ) :
    ((collectedSourceAtoms
      (inputWeight := inputWeight) e s).map fun atom => atom.value (n := n)).prod =
        (H s).collectedWeightProduct (n := n) (e s) := by
  by_cases hs : inputWeight ≤ s
  · simp [collectedSourceAtoms, hs,
      SSAtom.value,
      PEAddres.freeLowerTruncation,
      BCWta.collectedWeightProduct,
      BCWta.collected_lower_centralterm,
      BCWt.evalin_freelower_centtrunterm,
      Function.comp_def]
  · rw [heBelow s (Nat.lt_of_not_ge hs),
      BCWta.collected_weight_productzero]
    simp [collectedSourceAtoms, hs]

/-- Eligible source atoms through ordinary Hall weight `k`. -/
noncomputable def collectedPrefixAtoms
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (k : ℕ) :
    List (SSAtom H inputWeight) :=
  (List.range k).flatMap fun s =>
    collectedSourceAtoms e (s + 1)

/-- Prefix source-atom values multiply to the corresponding collected Hall prefix. -/
lemma collected_prefix_atoms
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (k : ℕ) :
    ((collectedPrefixAtoms
      (inputWeight := inputWeight) e k).map fun atom => atom.value (n := n)).prod =
        collectedPrefixProduct (n := n) H e k := by
  induction k with
  | zero =>
      simp [collectedPrefixAtoms, collectedPrefixProduct]
  | succ k ih =>
      rw [collectedPrefixAtoms, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, List.map_append, List.prod_append,
        collected_prefix_succ]
      change
        ((collectedPrefixAtoms
            (inputWeight := inputWeight) e k).map fun atom =>
              atom.value (n := n)).prod *
            ((collectedSourceAtoms
              (inputWeight := inputWeight) e (k + 1)).map fun atom =>
                atom.value (n := n)).prod =
          collectedPrefixProduct H e k *
            (H (k + 1)).collectedWeightProduct (e (k + 1))
      rw [ih,
        value_collected_atoms e heBelow]

/-- Eligible source atoms for the full collected Hall block. -/
noncomputable def collectedHallAtoms
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    List (SSAtom H inputWeight) :=
  collectedPrefixAtoms e (n - 1)

/-- Full source-atom values multiply to the original collected Hall block. -/
lemma list_collected_atoms
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    ((collectedHallAtoms
      (n := n) (inputWeight := inputWeight) e).map fun atom => atom.value (n := n)).prod =
        collectedHallProduct (n := n) H e := by
  exact collected_prefix_atoms e heBelow (n - 1)

/-- The untruncated explicit class-two powered source for a collected Hall block. -/
noncomputable def collectedTwoFactors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    List (SPFactora H inputWeight) :=
  SSAtom.factors
    (collectedHallAtoms (n := n) (inputWeight := inputWeight) e)

/-- The explicit class-two source evaluates to the power of the collected Hall block. -/
lemma collected_two_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (collectedTwoFactors (n := n)
          (inputWeight := inputWeight) e) =
      collectedHallProduct (n := n) H e ^ q := by
  rw [collectedTwoFactors,
    SSAtom.listEval_factors hinputWeight hcutoff,
    list_collected_atoms e heBelow]

/-- The physically truncated explicit class-two powered source. -/
noncomputable def truncatedSourceFactors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    List (SPFactora H inputWeight) :=
  SPFactora.truncate n
    (collectedTwoFactors (n := n)
      (inputWeight := inputWeight) e)

/-- Truncating the class-two source preserves its powered-block identity. -/
lemma list_truncated_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (truncatedSourceFactors (n := n)
          (inputWeight := inputWeight) e) =
      collectedHallProduct (n := n) H e ^ q := by
  rw [truncatedSourceFactors,
    SPFactora.listEval_truncate,
    collected_two_factors hinputWeight hcutoff e heBelow]

/-- The truncated class-two source is physically below the nilpotence cutoff. -/
lemma truncated_source_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    SPFactora.IsTruncated n
      (truncatedSourceFactors (n := n)
        (inputWeight := inputWeight) e) :=
  SPFactora.isTruncated_truncate _

namespace TCRun

/--
Package a recollection of the explicit class-two powered source as a complete
symbolic collection run.
-/
noncomputable def class_two_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (coordinates : CCExpans H inputWeight)
    (hrewrites :
      TSRwa (n := n)
        (truncatedSourceFactors
          (n := n) (inputWeight := inputWeight) e)
        (coordinates.factors (n := n))) :
    TCRun (n := n)
      (inputWeight := inputWeight) H e where
  source :=
    truncatedSourceFactors
      (n := n) (inputWeight := inputWeight) e
  coordinates := coordinates
  source_isTruncated :=
    truncated_source_factors e
  list_eval_source :=
    list_truncated_factors
      hinputWeight hcutoff e heBelow
  rewrites := hrewrites

end TCRun

/--
A recollection of the explicit class-two source supplies Claim 5 expansion
data throughout the region `n ≤ 3 * inputWeight`.
-/
theorem expansion_data_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (coordinates : CCExpans H inputWeight)
    (hrewrites :
      TSRwa (n := n)
        (truncatedSourceFactors
          (n := n) (inputWeight := inputWeight) e)
        (coordinates.factors (n := n))) :
    CEData (n := n) H e inputWeight :=
  (TCRun.class_two_rewrites
    hinputWeight hcutoff e heBelow coordinates hrewrites).coordinateExpansionData

/--
A recollection of the explicit class-two source supplies Claim 5 polynomial
data throughout the region `n ≤ 3 * inputWeight`.
-/
theorem collected_two_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (coordinates : CCExpans H inputWeight)
    (hrewrites :
      TSRwa (n := n)
        (truncatedSourceFactors
          (n := n) (inputWeight := inputWeight) e)
        (coordinates.factors (n := n))) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  (TCRun.class_two_rewrites
    hinputWeight hcutoff e heBelow coordinates hrewrites).coordinatePolynomialData
      hinputWeight

end TCTex
end Towers

-- Merged from ClassTwoScheduling.lean

/-!
# Scheduling class-two symbolic Hall power corrections

In the region `n ≤ 3 * inputWeight`, every explicit pair correction emitted by
the powered Hall source has weight at least `2 * inputWeight`.  It therefore
swaps past every factor of weight at least `inputWeight` without producing any
further retained correction.  Thus the surviving pair brackets form a central
layer for the remaining symbolic scheduler.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SSAtom

/-- A raw source factor has exactly the ordinary weight of its Hall address. -/
@[simp] lemma word_weight_factor
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atom : SSAtom H inputWeight) :
    atom.factor.word.weight PEAddres.weight =
      PEAddres.weight atom.address :=
  rfl

/-- Every raw source factor starts at the chosen initial weight. -/
lemma input_weight_factor
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atom : SSAtom H inputWeight) :
    inputWeight ≤ atom.factor.word.weight PEAddres.weight := by
  simpa using atom.inputWeight_le

/-- Every pair correction lies in the doubled initial-weight layer. -/
lemma input_pair_correction
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (later earlier : SSAtom H inputWeight) :
    2 * inputWeight ≤
      (later.pairCorrection earlier).word.weight
        PEAddres.weight := by
  rw [word_pair_correction]
  have hlater := later.inputWeight_le
  have hearlier := earlier.inputWeight_le
  omega

/--
In the class-two region, a pair correction and any eligible factor have total
weight at least the truncation cutoff.
-/
lemma n_pair_correction
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (x : SPFactora H inputWeight)
    (hx :
      inputWeight ≤ x.word.weight PEAddres.weight) :
    n ≤
      (later.pairCorrection earlier).word.weight
          PEAddres.weight +
        x.word.weight PEAddres.weight := by
  have hpair :=
    input_pair_correction later earlier
  omega

/-- The symmetric total-weight estimate for swapping an eligible factor left. -/
lemma n_pair_two
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (x : SPFactora H inputWeight)
    (hx :
      inputWeight ≤ x.word.weight PEAddres.weight) :
    n ≤
      x.word.weight PEAddres.weight +
        (later.pairCorrection earlier).word.weight
          PEAddres.weight := by
  have hpair :=
    input_pair_correction later earlier
  omega

/--
Every retained factor from one explicit pair-correction list lies between the
doubled initial weight and the truncation cutoff.
-/
lemma interval_truncate_corrections
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (earlier : SSAtom H inputWeight)
    (later : List (SSAtom H inputWeight))
    {x : SPFactora H inputWeight}
    (hx :
      x ∈ SPFactora.truncate n
        (pairCorrections earlier later)) :
    2 * inputWeight ≤
        x.word.weight PEAddres.weight ∧
      x.word.weight PEAddres.weight < n := by
  have hmem : x ∈ pairCorrections earlier later := by
    exact (List.mem_filter.mp hx).1
  constructor
  · rcases List.mem_map.mp hmem with ⟨atom, _hatom, rfl⟩
    exact input_pair_correction atom earlier
  · exact SPFactora.word_weight_truncate hx

/-- Every factor in the explicit class-two source remains above the initial weight. -/
lemma input_weight_factors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    ∀ (atoms : List (SSAtom H inputWeight))
      {x : SPFactora H inputWeight},
      x ∈ factors atoms →
        inputWeight ≤ x.word.weight PEAddres.weight := by
  intro atoms
  induction atoms with
  | nil =>
      simp [factors]
  | cons atom atoms ih =>
      intro x hx
      rw [factors] at hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_map.mp hx with ⟨later, _hlater, rfl⟩
          have hpair :=
            input_pair_correction later atom
          omega
        · rcases List.mem_singleton.mp hx with rfl
          exact atom.input_weight_factor
      · exact ih hx

/-- Physical truncation preserves the initial-weight lower bound. -/
lemma input_truncate_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atoms : List (SSAtom H inputWeight))
    {x : SPFactora H inputWeight}
    (hx : x ∈ SPFactora.truncate n (factors atoms)) :
    inputWeight ≤ x.word.weight PEAddres.weight :=
  input_weight_factors atoms (List.mem_filter.mp hx).1

end SSAtom

namespace TCPkt

/-- A pair correction swaps rightward past every eligible factor without output. -/
def empty_pair_correction
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (x : SPFactora H inputWeight)
    (hx :
      inputWeight ≤ x.word.weight PEAddres.weight) :
    TCPkt n
      (later.pairCorrection earlier) x :=
  empty_n_weight (later.pairCorrection earlier) x
    (SSAtom.n_pair_correction
      hcutoff later earlier x hx)

/-- An eligible factor swaps rightward past a pair correction without output. -/
def empty_pair_two
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (x : SPFactora H inputWeight)
    (hx :
      inputWeight ≤ x.word.weight PEAddres.weight) :
    TCPkt n x
      (later.pairCorrection earlier) :=
  empty_n_weight x (later.pairCorrection earlier)
    (SSAtom.n_pair_two
      hcutoff later earlier x hx)

/-- A pair correction swaps past every factor in an explicit class-two source. -/
def empty_left_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (atoms : List (SSAtom H inputWeight))
    (x : SPFactora H inputWeight)
    (hx : x ∈ SSAtom.factors atoms) :
    TCPkt n
      (later.pairCorrection earlier) x :=
  empty_pair_correction hcutoff later earlier x
    (SSAtom.input_weight_factors
      atoms hx)

/-- Every explicit class-two source factor swaps past a pair correction without output. -/
def empty_pair_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (atoms : List (SSAtom H inputWeight))
    (x : SPFactora H inputWeight)
    (hx : x ∈ SSAtom.factors atoms) :
    TCPkt n x
      (later.pairCorrection earlier) :=
  empty_pair_two hcutoff later earlier x
    (SSAtom.input_weight_factors
      atoms hx)

end TCPkt

namespace TSStep

/-- Move a pair correction rightward past an eligible factor with no output. -/
def obstruction_empty_two
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (x : SPFactora H inputWeight)
    (hx :
      inputWeight ≤ x.word.weight PEAddres.weight) :
    TSStep (n := n) H inputWeight
      (P ++ [later.pairCorrection earlier, x] ++ S)
      (P ++ [x, later.pairCorrection earlier] ++ S) :=
  obstrucempty_nle_addwordweight P S
    (later.pairCorrection earlier) x
    (SSAtom.n_pair_correction
      hcutoff later earlier x hx)

/-- Move an eligible factor rightward past a pair correction with no output. -/
def obstruction_pair_empty
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (x : SPFactora H inputWeight)
    (hx :
      inputWeight ≤ x.word.weight PEAddres.weight) :
    TSStep (n := n) H inputWeight
      (P ++ [x, later.pairCorrection earlier] ++ S)
      (P ++ [later.pairCorrection earlier, x] ++ S) :=
  obstrucempty_nle_addwordweight P S x
    (later.pairCorrection earlier)
    (SSAtom.n_pair_two
      hcutoff later earlier x hx)

end TSStep

namespace TSRwa

/-- Bubble one explicit pair correction rightward across an eligible block. -/
lemma move_pair_correction
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (L : List (SPFactora H inputWeight))
    (hL :
      ∀ x ∈ L,
        inputWeight ≤ x.word.weight PEAddres.weight) :
    TSRwa (n := n)
      (P ++ [later.pairCorrection earlier] ++ L ++ S)
      (P ++ L ++ [later.pairCorrection earlier] ++ S) :=
  move_left_across P S (later.pairCorrection earlier) L fun x hx =>
    SSAtom.n_pair_correction
      hcutoff later earlier x (hL x hx)

/-- Bubble one explicit pair correction leftward across an eligible block. -/
lemma move_pair_two
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (hcutoff : n ≤ 3 * inputWeight)
    (later earlier : SSAtom H inputWeight)
    (L : List (SPFactora H inputWeight))
    (hL :
      ∀ x ∈ L,
        inputWeight ≤ x.word.weight PEAddres.weight) :
    TSRwa (n := n)
      (P ++ L ++ [later.pairCorrection earlier] ++ S)
      (P ++ [later.pairCorrection earlier] ++ L ++ S) :=
  move_right_across P S (later.pairCorrection earlier) L fun x hx =>
    SSAtom.n_pair_two
      hcutoff later earlier x (hL x hx)

/-- Bubble a whole explicit pair-correction block rightward across eligible factors. -/
lemma move_pair_corrections
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (hcutoff : n ≤ 3 * inputWeight)
    (earlier : SSAtom H inputWeight)
    (later : List (SSAtom H inputWeight))
    (L : List (SPFactora H inputWeight))
    (hL :
      ∀ x ∈ L,
        inputWeight ≤ x.word.weight PEAddres.weight) :
    TSRwa (n := n)
      (P ++ SSAtom.pairCorrections earlier later ++ L ++ S)
      (P ++ L ++ SSAtom.pairCorrections earlier later ++ S) := by
  apply move_left_block
  intro B hB x hx
  rcases List.mem_map.mp hB with ⟨atom, _hatom, rfl⟩
  exact
    SSAtom.n_pair_correction
      hcutoff atom earlier x (hL x hx)

/--
Bubble the retained part of a pair-correction block rightward across eligible
factors.
-/
lemma move_truncate_corrections
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P S : List (SPFactora H inputWeight))
    (hcutoff : n ≤ 3 * inputWeight)
    (earlier : SSAtom H inputWeight)
    (later : List (SSAtom H inputWeight))
    (L : List (SPFactora H inputWeight))
    (hL :
      ∀ x ∈ L,
        inputWeight ≤ x.word.weight PEAddres.weight) :
    TSRwa (n := n)
      (P ++
        SPFactora.truncate n
          (SSAtom.pairCorrections earlier later) ++
        L ++ S)
      (P ++ L ++
        SPFactora.truncate n
          (SSAtom.pairCorrections earlier later) ++
        S) := by
  apply move_left_block
  intro B hB x hx
  have hB' :
      B ∈ SSAtom.pairCorrections earlier later :=
    (List.mem_filter.mp hB).1
  rcases List.mem_map.mp hB' with ⟨atom, _hatom, rfl⟩
  exact
    SSAtom.n_pair_correction
      hcutoff atom earlier x (hL x hx)

end TSRwa

end TCTex
end Towers

-- Merged from ClassTwoCentralization.lean

/-!
# Centralizing the class-two symbolic Hall power source

The explicit class-two powered source interleaves raw `choose q 1` factors with
central `choose q 2` pair corrections.  This file constructs a finite truncated
rewrite run that moves every pair correction to a final central tail.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open TSRwa

/-- Truncation of a cons splits into its singleton head and tail. -/
lemma SPFactora.truncate_cons
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (x : SPFactora H inputWeight)
    (L : List (SPFactora H inputWeight)) :
    SPFactora.truncate n (x :: L) =
      SPFactora.truncate n [x] ++
        SPFactora.truncate n L := by
  change
    SPFactora.truncate n ([x] ++ L) =
      SPFactora.truncate n [x] ++
        SPFactora.truncate n L
  rw [SPFactora.truncate_append]

namespace SSAtom

/-- The raw `choose q 1` factors attached to an ordered source-atom list. -/
def atomicFactors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atoms : List (SSAtom H inputWeight)) :
    List (SPFactora H inputWeight) :=
  atoms.map factor

/-- All `choose q 2` pair corrections, retained in their recursive source order. -/
def centralPairCorrections
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    List (SSAtom H inputWeight) →
      List (SPFactora H inputWeight)
  | [] => []
  | atom :: atoms =>
      pairCorrections atom atoms ++ centralPairCorrections atoms

/-- Every raw atomic factor remains above the initial weight. -/
lemma input_atomic_factors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atoms : List (SSAtom H inputWeight))
    {x : SPFactora H inputWeight}
    (hx : x ∈ atomicFactors atoms) :
    inputWeight ≤ x.word.weight PEAddres.weight := by
  rcases List.mem_map.mp hx with ⟨atom, _hatom, rfl⟩
  exact atom.input_weight_factor

/-- Truncation preserves the initial-weight lower bound for raw atomic factors. -/
lemma input_truncate_atomic
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (atoms : List (SSAtom H inputWeight))
    {x : SPFactora H inputWeight}
    (hx : x ∈ SPFactora.truncate n (atomicFactors atoms)) :
    inputWeight ≤ x.word.weight PEAddres.weight :=
  input_atomic_factors atoms (List.mem_filter.mp hx).1

/-- Every central pair correction lies in the doubled initial-weight layer. -/
lemma input_pair_corrections
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s} :
    ∀ (atoms : List (SSAtom H inputWeight))
      {x : SPFactora H inputWeight},
      x ∈ centralPairCorrections atoms →
        2 * inputWeight ≤
          x.word.weight PEAddres.weight := by
  intro atoms
  induction atoms with
  | nil =>
      simp [centralPairCorrections]
  | cons atom atoms ih =>
      intro x hx
      rw [centralPairCorrections] at hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_map.mp hx with ⟨later, _hlater, rfl⟩
        exact input_pair_correction later atom
      · exact ih hx

/--
Centralize the untruncated explicit class-two source: raw atoms move to the
front and all pair corrections move to a final tail.
-/
lemma rewrites_atomic_corrections
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight) :
    ∀ atoms : List (SSAtom H inputWeight),
      TSRwa (n := n)
        (factors atoms)
        (atomicFactors atoms ++ centralPairCorrections atoms) := by
  intro atoms
  induction atoms with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons atom atoms ih =>
      have htail :
          TSRwa (n := n)
            (pairCorrections atom atoms ++ [atom.factor] ++ factors atoms)
            (pairCorrections atom atoms ++ [atom.factor] ++
              (atomicFactors atoms ++ centralPairCorrections atoms)) := by
        simpa [List.append_assoc] using
          ih.context (pairCorrections atom atoms ++ [atom.factor]) []
      have hmove :
          TSRwa (n := n)
            (pairCorrections atom atoms ++
              (atom.factor :: atomicFactors atoms) ++
              centralPairCorrections atoms)
            ((atom.factor :: atomicFactors atoms) ++
              pairCorrections atom atoms ++
              centralPairCorrections atoms) := by
        apply
          TSRwa.move_pair_corrections
            [] (centralPairCorrections atoms) hcutoff atom atoms
              (atom.factor :: atomicFactors atoms)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact atom.input_weight_factor
        · exact input_atomic_factors atoms hx
      have hmove' :
          TSRwa (n := n)
            (pairCorrections atom atoms ++ [atom.factor] ++
              (atomicFactors atoms ++ centralPairCorrections atoms))
            ((atom.factor :: atomicFactors atoms) ++
              (pairCorrections atom atoms ++ centralPairCorrections atoms)) := by
        simpa [List.append_assoc] using hmove
      exact (by
        simpa [factors, atomicFactors, centralPairCorrections, List.append_assoc] using
          htail.trans hmove')

/--
Centralize the physically retained class-two source.  The resulting target is
the retained raw atomic block followed by the retained central correction tail.
-/
lemma truncate_atomic_corrections
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight) :
    ∀ atoms : List (SSAtom H inputWeight),
      TSRwa (n := n)
        (SPFactora.truncate n (factors atoms))
        (SPFactora.truncate n (atomicFactors atoms) ++
          SPFactora.truncate n (centralPairCorrections atoms)) := by
  intro atoms
  induction atoms with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons atom atoms ih =>
      have htail :
          TSRwa (n := n)
            (SPFactora.truncate n (pairCorrections atom atoms) ++
              SPFactora.truncate n [atom.factor] ++
              SPFactora.truncate n (factors atoms))
            (SPFactora.truncate n (pairCorrections atom atoms) ++
              SPFactora.truncate n [atom.factor] ++
              (SPFactora.truncate n (atomicFactors atoms) ++
                SPFactora.truncate n
                  (centralPairCorrections atoms))) := by
        simpa [List.append_assoc] using
          ih.context
            (SPFactora.truncate n (pairCorrections atom atoms) ++
              SPFactora.truncate n [atom.factor]) []
      have hmove :
          TSRwa (n := n)
            (SPFactora.truncate n (pairCorrections atom atoms) ++
              (SPFactora.truncate n [atom.factor] ++
                SPFactora.truncate n (atomicFactors atoms)) ++
              SPFactora.truncate n (centralPairCorrections atoms))
            ((SPFactora.truncate n [atom.factor] ++
                SPFactora.truncate n (atomicFactors atoms)) ++
              SPFactora.truncate n (pairCorrections atom atoms) ++
              SPFactora.truncate n
                (centralPairCorrections atoms)) := by
        apply
          move_truncate_corrections
            [] (SPFactora.truncate n
              (centralPairCorrections atoms))
            hcutoff atom atoms
            (SPFactora.truncate n [atom.factor] ++
              SPFactora.truncate n (atomicFactors atoms))
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have hx' : x = atom.factor := by
            simpa using (List.mem_filter.mp hx).1
          rw [hx']
          exact atom.input_weight_factor
        · exact input_truncate_atomic atoms hx
      have hmove' :
          TSRwa (n := n)
            (SPFactora.truncate n (pairCorrections atom atoms) ++
              SPFactora.truncate n [atom.factor] ++
              (SPFactora.truncate n (atomicFactors atoms) ++
                SPFactora.truncate n
                  (centralPairCorrections atoms)))
            ((SPFactora.truncate n [atom.factor] ++
                SPFactora.truncate n (atomicFactors atoms)) ++
              (SPFactora.truncate n (pairCorrections atom atoms) ++
                SPFactora.truncate n
                  (centralPairCorrections atoms))) := by
        simpa [List.append_assoc] using hmove
      have hsource :
          SPFactora.truncate n (factors (atom :: atoms)) =
            SPFactora.truncate n (pairCorrections atom atoms) ++
              SPFactora.truncate n [atom.factor] ++
                SPFactora.truncate n (factors atoms) := by
        rw [factors, SPFactora.truncate_append,
          SPFactora.truncate_append]
      have htarget :
          SPFactora.truncate n (atomicFactors (atom :: atoms)) ++
                SPFactora.truncate n
                  (centralPairCorrections (atom :: atoms)) =
            (SPFactora.truncate n [atom.factor] ++
                SPFactora.truncate n (atomicFactors atoms)) ++
              (SPFactora.truncate n (pairCorrections atom atoms) ++
                SPFactora.truncate n
                  (centralPairCorrections atoms)) := by
        have hatomic :
            SPFactora.truncate n
                (atomicFactors (atom :: atoms)) =
              SPFactora.truncate n [atom.factor] ++
                SPFactora.truncate n (atomicFactors atoms) := by
          change
            SPFactora.truncate n
                (atom.factor :: atomicFactors atoms) =
              SPFactora.truncate n [atom.factor] ++
                SPFactora.truncate n (atomicFactors atoms)
          exact SPFactora.truncate_cons atom.factor _
        have hcentral :
            SPFactora.truncate n
                (centralPairCorrections (atom :: atoms)) =
              SPFactora.truncate n (pairCorrections atom atoms) ++
                SPFactora.truncate n
                  (centralPairCorrections atoms) := by
          rw [centralPairCorrections,
            SPFactora.truncate_append]
        rw [hatomic, hcentral]
      rw [hsource, htarget]
      simpa [List.append_assoc] using htail.trans hmove'

end SSAtom

open SSAtom

/-- The centralized, physically truncated class-two powered source. -/
noncomputable def truncatedCentralizedFactors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    List (SPFactora H inputWeight) :=
  SPFactora.truncate n
      (SSAtom.atomicFactors
        (collectedHallAtoms (n := n)
          (inputWeight := inputWeight) e)) ++
    SPFactora.truncate n
      (SSAtom.centralPairCorrections
        (collectedHallAtoms (n := n)
          (inputWeight := inputWeight) e))

/-- The explicit class-two source rewrites to its centralized retained form. -/
lemma truncated_rewrites_centralized
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H) :
    TSRwa (n := n)
      (truncatedSourceFactors
        (n := n) (inputWeight := inputWeight) e)
      (truncatedCentralizedFactors
        (n := n) (inputWeight := inputWeight) e) := by
  exact
    truncate_atomic_corrections
      hcutoff
      (collectedHallAtoms (n := n) (inputWeight := inputWeight) e)

/-- The centralized retained class-two source still evaluates to the powered Hall block. -/
lemma collected_centralized_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (truncatedCentralizedFactors
          (n := n) (inputWeight := inputWeight) e) =
      collectedHallProduct (n := n) H e ^ q := by
  exact
    (truncated_rewrites_centralized
      hcutoff e).listEval_eq q |>.trans
        (list_truncated_factors
          hinputWeight hcutoff e heBelow q)

end TCTex
end Towers

-- Merged from ClassTwoAtomicEndpoint.lean

/-!
# The atomic endpoint of class-two symbolic Hall powers

After centralizing the explicit class-two powered source, its raw atomic prefix
is exactly the normalized coordinatewise-scaled Hall endpoint already used in
the commutative terminal region.  Only the central `choose q 2` correction tail
remains to be normalized.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SSAtom

/-- In one Hall-weight layer, raw atomic factors are the scaled-coordinate endpoint. -/
lemma atomic_collected_atoms
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (s : ℕ) :
    atomicFactors
        (collectedSourceAtoms
          (inputWeight := inputWeight) e s) =
      (scaledCoordinateExpansions
        (inputWeight := inputWeight) e).weightFactors s := by
  by_cases hs : inputWeight ≤ s
  · simp only [atomicFactors, collectedSourceAtoms, hs,
      dif_pos, scaledCoordinateExpansions,
      CCExpans.weightFactors,
      scaledCoordinateExpansion,
      BCExp.symbolicPowerFactors]
    induction (Finset.univ.sort fun i i' : (H s).index => i ≤ i') with
    | nil =>
        rfl
    | cons i indices ih =>
        simp [SPFactora.coordinateExpansion,
          BRTerm.symbolicPowerFactor,
          SPFactora.source, factor, ih]
  · simp only [atomicFactors, collectedSourceAtoms, hs,
      scaledCoordinateExpansions,
      CCExpans.weightFactors]
    symm
    apply List.flatMap_eq_nil_iff.2
    intro i _hi
    rw [scaledCoordinateExpansion, dif_neg hs]
    rfl

/-- Through every weight prefix, raw atomic factors are the scaled endpoint. -/
lemma atomic_prefix_atoms
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (k : ℕ) :
    atomicFactors
        (collectedPrefixAtoms
          (inputWeight := inputWeight) e k) =
      (scaledCoordinateExpansions
        (inputWeight := inputWeight) e).prefixFactors k := by
  induction k with
  | zero =>
      simp [atomicFactors, collectedPrefixAtoms,
        CCExpans.prefixFactors]
  | succ k ih =>
      rw [collectedPrefixAtoms, List.range_succ,
        List.flatMap_append, List.flatMap_singleton, atomicFactors,
        List.map_append, CCExpans.prefixFactors,
        List.range_succ, List.flatMap_append, List.flatMap_singleton]
      change
        atomicFactors
              (collectedPrefixAtoms
                (inputWeight := inputWeight) e k) ++
            atomicFactors
              (collectedSourceAtoms
                (inputWeight := inputWeight) e (k + 1)) =
          (scaledCoordinateExpansions
              (inputWeight := inputWeight) e).prefixFactors k ++
            (scaledCoordinateExpansions
              (inputWeight := inputWeight) e).weightFactors (k + 1)
      rw [ih, atomic_collected_atoms]

/-- For the full block, raw atomic factors are the scaled-coordinate endpoint. -/
lemma atomic_factors_atoms
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    atomicFactors
        (collectedHallAtoms
          (n := n) (inputWeight := inputWeight) e) =
      (scaledCoordinateExpansions
        (inputWeight := inputWeight) e).factors (n := n) :=
  atomic_prefix_atoms e (n - 1)

end SSAtom

/-- The physically retained central correction tail of the class-two source. -/
noncomputable def truncatedCorrectionFactors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    List (SPFactora H inputWeight) :=
  SPFactora.truncate n
    (SSAtom.centralPairCorrections
      (collectedHallAtoms (n := n)
        (inputWeight := inputWeight) e))

/--
The centralized retained source is the scaled Hall endpoint followed by the
retained central correction tail.
-/
lemma centralized_scaled_corrections
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    truncatedCentralizedFactors
        (n := n) (inputWeight := inputWeight) e =
      (scaledCoordinateExpansions
          (inputWeight := inputWeight) e).factors (n := n) ++
        truncatedCorrectionFactors
          (n := n) (inputWeight := inputWeight) e := by
  rw [truncatedCentralizedFactors,
    truncatedCorrectionFactors,
    SSAtom.atomic_factors_atoms,
    SPFactora.truncate_self_truncated
      (scaledCoordinateExpansions
        (inputWeight := inputWeight) e).isTruncated_factors]

/--
The explicit class-two powered source rewrites to the scaled Hall endpoint plus
one central correction tail.
-/
lemma rewrites_scaled_corrections
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H) :
    TSRwa (n := n)
      (truncatedSourceFactors
        (n := n) (inputWeight := inputWeight) e)
      ((scaledCoordinateExpansions
          (inputWeight := inputWeight) e).factors (n := n) ++
        truncatedCorrectionFactors
          (n := n) (inputWeight := inputWeight) e) := by
  rw [←
    centralized_scaled_corrections
      e]
  exact
    truncated_rewrites_centralized
      hcutoff e

end TCTex
end Towers

-- Merged from ClassTwoTailAdapter.lean

/-!
# Tail-only class-two symbolic Hall power adapters

In the class-two region, the explicit powered source rewrites to the scaled
Hall endpoint followed by one retained central correction tail.  Consequently,
a normalizer for that reduced endpoint is enough to construct the Claim 5
coordinate expansion and integer-valued polynomial data.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TCRun

/--
Package a normalization of only the scaled endpoint plus its retained central
correction tail as a complete symbolic collection run.
-/
noncomputable def two_tail_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (coordinates : CCExpans H inputWeight)
    (hrewritesTail :
      TSRwa (n := n)
        ((scaledCoordinateExpansions
            (inputWeight := inputWeight) e).factors (n := n) ++
          truncatedCorrectionFactors
            (n := n) (inputWeight := inputWeight) e)
        (coordinates.factors (n := n))) :
    TCRun (n := n)
      (inputWeight := inputWeight) H e :=
  class_two_rewrites hinputWeight hcutoff e heBelow coordinates
    ((rewrites_scaled_corrections
      hcutoff e).trans hrewritesTail)

end TCRun

/--
A normalization of the reduced class-two endpoint supplies Claim 5 expansion
data throughout the region `n ≤ 3 * inputWeight`.
-/
theorem collected_coordinate_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (coordinates : CCExpans H inputWeight)
    (hrewritesTail :
      TSRwa (n := n)
        ((scaledCoordinateExpansions
            (inputWeight := inputWeight) e).factors (n := n) ++
          truncatedCorrectionFactors
            (n := n) (inputWeight := inputWeight) e)
        (coordinates.factors (n := n))) :
    CEData (n := n) H e inputWeight :=
  (TCRun.two_tail_rewrites
    hinputWeight hcutoff e heBelow coordinates
      hrewritesTail).coordinateExpansionData

/--
A normalization of the reduced class-two endpoint supplies Claim 5
integer-valued polynomial data throughout the region `n ≤ 3 * inputWeight`.
-/
theorem collected_data_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (coordinates : CCExpans H inputWeight)
    (hrewritesTail :
      TSRwa (n := n)
        ((scaledCoordinateExpansions
            (inputWeight := inputWeight) e).factors (n := n) ++
          truncatedCorrectionFactors
            (n := n) (inputWeight := inputWeight) e)
        (coordinates.factors (n := n))) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  (TCRun.two_tail_rewrites
    hinputWeight hcutoff e heBelow coordinates
      hrewritesTail).coordinatePolynomialData hinputWeight

end TCTex
end Towers

-- Merged from ClassTwoCoordinateMerge.lean

/-!
# Coordinate merges for class-two symbolic Hall powers

Coordinatewise addition of explicit Hall expansions interleaves their factors
by Hall address.  This file proves the required stable shuffle as an actual
finite truncated rewrite run whenever all cross-pairs have empty correction
packets.  In the class-two region, that condition follows from the weight
split between scaled atoms and normalized central corrections.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TSRwa

/-- Lift coordinatewise finite rewrite runs through one finite concatenation. -/
lemma flat_forall
    {ι : Type*}
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (indices : List ι)
    (left right : ι → List (SPFactora H inputWeight))
    (hrewrites :
      ∀ i ∈ indices,
        TSRwa (n := n)
          (left i) (right i)) :
    TSRwa (n := n)
      (indices.flatMap left) (indices.flatMap right) := by
  induction indices with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons i indices ih =>
      simpa using
        (hrewrites i (by simp)).append
          (ih fun j hj => hrewrites j (by simp [hj]))

/--
Stably interleave two lists of factor blocks.  Each right block bubbles left
across the later left blocks, using only empty adjacent correction packets.
-/
lemma append_flat_rewrites
    {ι : Type*}
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (indices : List ι)
    (left right : ι → List (SPFactora H inputWeight))
    (hcross :
      ∀ B ∈ indices.flatMap left, ∀ A ∈ indices.flatMap right,
        n ≤ B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight) :
    TSRwa (n := n)
      (indices.flatMap left ++ indices.flatMap right)
      (indices.flatMap fun i => left i ++ right i) := by
  induction indices with
  | nil =>
      exact Relation.ReflTransGen.refl
  | cons i indices ih =>
      have hmove :
          TSRwa (n := n)
            (left i ++ indices.flatMap left ++ right i ++ indices.flatMap right)
            (left i ++ right i ++ indices.flatMap left ++ indices.flatMap right) := by
        apply move_left_block
        intro B hB A hA
        exact hcross B (by simp [hB]) A (by simp [hA])
      have htail :
          TSRwa (n := n)
            (indices.flatMap left ++ indices.flatMap right)
            (indices.flatMap fun j => left j ++ right j) :=
        ih fun B hB A hA => hcross B (by simp [hB]) A (by simp [hA])
      have htail' :
          TSRwa (n := n)
            (left i ++ right i ++ indices.flatMap left ++ indices.flatMap right)
            (left i ++ right i ++
              (indices.flatMap fun j => left j ++ right j)) := by
        simpa [List.append_assoc] using
          htail.context (left i ++ right i) []
      exact (by
        simpa [List.append_assoc] using
          hmove.trans htail')

end TSRwa

namespace BCExp

/-- Attaching Hall words to an added expansion concatenates the attached factors. -/
@[simp]
lemma symbolic_factors_add
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (word : CWord (HEAddres H))
    (left right :
      BCExp inputWeight
        (word.weight PEAddres.weight)) :
    (left.add right).symbolicPowerFactors word =
      left.symbolicPowerFactors word ++
        right.symbolicPowerFactors word := by
  simp [BCExp.add, symbolicPowerFactors]

end BCExp

namespace CCExpans

/-- Add two normalized Hall coordinate expansions coordinatewise. -/
def add
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (left right : CCExpans H inputWeight) :
    CCExpans H inputWeight where
  expansion s i := (left.expansion s i).add (right.expansion s i)

/-- Coordinatewise addition adds the evaluated Hall exponents. -/
@[simp]
lemma eval_add
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (left right : CCExpans H inputWeight)
    (q : ℕ) :
    (left.add right).eval q = left.eval q + right.eval q := by
  funext s i
  simp [add, eval]

/--
The concatenated factors in one Hall-weight layer rewrite to the interleaved
factors of the coordinatewise sum.
-/
lemma append_rewrites_add
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (left right : CCExpans H inputWeight)
    (s : ℕ)
    (hcross :
      ∀ B ∈ left.weightFactors s, ∀ A ∈ right.weightFactors s,
        n ≤ B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight) :
    TSRwa (n := n)
      (left.weightFactors s ++ right.weightFactors s)
      ((left.add right).weightFactors s) := by
  unfold weightFactors
  dsimp only [add]
  convert
    (TSRwa.append_flat_rewrites
      (n := n) (Finset.univ.sort fun i i' : (H s).index => i ≤ i')
      (fun i =>
        (left.expansion s i).symbolicPowerFactors
          (.atom (⟨s, i⟩ : HEAddres H)))
      (fun i =>
        (right.expansion s i).symbolicPowerFactors
          (.atom (⟨s, i⟩ : HEAddres H)))
      hcross) using 1
  induction (Finset.univ.sort fun i i' : (H s).index => i ≤ i') with
  | nil =>
      rfl
  | cons i indices ih =>
      simp only [List.flatMap_cons]
      have hhead :
          ((left.expansion s i).add
              (right.expansion s i)).symbolicPowerFactors
                (.atom (⟨s, i⟩ : HEAddres H)) =
            (left.expansion s i).symbolicPowerFactors
                (.atom (⟨s, i⟩ : HEAddres H)) ++
              (right.expansion s i).symbolicPowerFactors
                (.atom (⟨s, i⟩ : HEAddres H)) :=
        BCExp.symbolic_factors_add _ _ _
      rw [hhead, ih, List.append_assoc]

/--
The concatenated normalized prefixes rewrite to the prefix represented by
coordinatewise addition.
-/
lemma prefix_append_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (left right : CCExpans H inputWeight)
    (k : ℕ)
    (hcross :
      ∀ B ∈ left.prefixFactors k, ∀ A ∈ right.prefixFactors k,
        n ≤ B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight) :
    TSRwa (n := n)
      (left.prefixFactors k ++ right.prefixFactors k)
      ((left.add right).prefixFactors k) := by
  have hreorder :
      TSRwa (n := n)
        (((List.range k).flatMap fun s => left.weightFactors (s + 1)) ++
          ((List.range k).flatMap fun s => right.weightFactors (s + 1)))
        ((List.range k).flatMap fun s =>
          left.weightFactors (s + 1) ++ right.weightFactors (s + 1)) := by
    apply
      TSRwa.append_flat_rewrites
    intro B hB A hA
    exact hcross B (by simpa [prefixFactors] using hB) A
      (by simpa [prefixFactors] using hA)
  have hweights :
      TSRwa (n := n)
        ((List.range k).flatMap fun s =>
          left.weightFactors (s + 1) ++ right.weightFactors (s + 1))
        ((List.range k).flatMap fun s =>
          (left.add right).weightFactors (s + 1)) := by
    apply TSRwa.flat_forall
    intro s hs
    apply append_rewrites_add
    intro B hB A hA
    apply hcross B
    · exact List.mem_flatMap.mpr ⟨s, hs, hB⟩
    · exact List.mem_flatMap.mpr ⟨s, hs, hA⟩
  simpa only [prefixFactors] using hreorder.trans hweights

/--
The concatenated full normalized endpoints rewrite to the endpoint represented
by coordinatewise addition.
-/
lemma factors_append_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (left right : CCExpans H inputWeight)
    (hcross :
      ∀ B ∈ left.factors (n := n), ∀ A ∈ right.factors (n := n),
        n ≤ B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight) :
    TSRwa (n := n)
      (left.factors (n := n) ++ right.factors (n := n))
      ((left.add right).factors (n := n)) := by
  simpa only [factors] using
    left.prefix_append_rewrites right (n - 1) hcross

end CCExpans

/-- Scaled endpoint factors remain above the initial nonzero Hall weight. -/
lemma input_scaled_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    {x : SPFactora H inputWeight}
    (hx :
      x ∈ (scaledCoordinateExpansions
        (inputWeight := inputWeight) e).factors (n := n)) :
    inputWeight ≤ x.word.weight PEAddres.weight := by
  rw [←
    SSAtom.atomic_factors_atoms
      (n := n) (inputWeight := inputWeight) e] at hx
  exact
    SSAtom.input_atomic_factors
      _ hx

/-- The retained class-two correction tail starts in doubled initial weight. -/
lemma least_truncated_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    SPFactora.WordWeightLeast (2 * inputWeight)
      (truncatedCorrectionFactors
        (n := n) (inputWeight := inputWeight) e) := by
  apply SPFactora.word_least_truncate
  intro x hx
  exact
    SSAtom.input_pair_corrections
      _ hx

/--
In the class-two region, normalized correction coordinates supported in
weights at least `2 * inputWeight` merge automa with the scaled
coordinate endpoint.
-/
lemma scaled_corrections_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (corrections : CCExpans H inputWeight)
    (hcorrections :
      ∀ x ∈ corrections.factors (n := n),
        2 * inputWeight ≤
          x.word.weight PEAddres.weight) :
    TSRwa (n := n)
      ((scaledCoordinateExpansions
          (inputWeight := inputWeight) e).factors (n := n) ++
        corrections.factors (n := n))
      (((scaledCoordinateExpansions
          (inputWeight := inputWeight) e).add corrections).factors (n := n)) := by
  apply
    CCExpans.factors_append_rewrites
  intro B hB A hA
  have hscaled :=
    input_scaled_factors e hB
  have hcorrection := hcorrections A hA
  omega

namespace TCRun

/--
Package a normalization of the retained central correction tail.  Its merge
with the scaled endpoint is automatic once the normalized correction factors
remain in doubled initial weight.
-/
noncomputable def class_tail_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (corrections : CCExpans H inputWeight)
    (hrewritesCorrections :
      TSRwa (n := n)
        (truncatedCorrectionFactors
          (n := n) (inputWeight := inputWeight) e)
        (corrections.factors (n := n))) :
    TCRun (n := n)
      (inputWeight := inputWeight) H e :=
  two_tail_rewrites hinputWeight hcutoff e heBelow
    ((scaledCoordinateExpansions
      (inputWeight := inputWeight) e).add corrections)
    ((TSRwa.append
      (Relation.ReflTransGen.refl :
        TSRwa (n := n)
          (scaledCoordinateExpansions
            (inputWeight := inputWeight) e).factors
          (scaledCoordinateExpansions
            (inputWeight := inputWeight) e).factors)
      hrewritesCorrections).trans
      (scaled_corrections_rewrites
        hcutoff e corrections
          (hrewritesCorrections.wordWeightLeast
            (least_truncated_factors
              e))))

end TCRun

/--
A normalization of only the retained central correction tail supplies Claim 5
expansion data throughout the class-two region.
-/
theorem collected_expansion_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (corrections : CCExpans H inputWeight)
    (hrewritesCorrections :
      TSRwa (n := n)
        (truncatedCorrectionFactors
          (n := n) (inputWeight := inputWeight) e)
        (corrections.factors (n := n))) :
    CEData (n := n) H e inputWeight :=
  (TCRun.class_tail_rewrites
    hinputWeight hcutoff e heBelow corrections
      hrewritesCorrections).coordinateExpansionData

/--
A normalization of only the retained central correction tail supplies Claim 5
integer-valued polynomial data throughout the class-two region.
-/
theorem collected_tail_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (corrections : CCExpans H inputWeight)
    (hrewritesCorrections :
      TSRwa (n := n)
        (truncatedCorrectionFactors
          (n := n) (inputWeight := inputWeight) e)
        (corrections.factors (n := n))) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  (TCRun.class_tail_rewrites
    hinputWeight hcutoff e heBelow corrections
      hrewritesCorrections).coordinatePolynomialData hinputWeight

end TCTex
end Towers

-- Merged from ClassTwoSemanticTail.lean

/-!
# Semantic normalization of the class-two correction tail

Adjacent Hall swaps cannot replace one internal bracket word by its collected
Hall-coordinate factors.  In the class-two correction tail those bracket
values lie in a commutative high-weight lower-central region.  We may therefore
choose their semantic Hall normal forms, multiply the constant coordinates by
the original symbolic recipe, and prove directly that the normalized atomic
endpoint has the same value.
-/

namespace Towers
namespace TCTex

universe u

namespace CCExpans

/-- The coordinate expansion with no terms in any Hall coordinate. -/
def zero
    {d : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (inputWeight : ℕ) :
    CCExpans H inputWeight where
  expansion s _ := BCExp.zero inputWeight s

/-- No coordinate expansion has a term below `lowerWeight`. -/
def NTBelow
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (lowerWeight : ℕ)
    (R : CCExpans H inputWeight) :
    Prop :=
  ∀ s i, s < lowerWeight → (R.expansion s i).terms = []

/-- The empty coordinate expansion has no terms below every lower bound. -/
lemma no_below_zero
    {d inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) :
    (zero H inputWeight).NTBelow lowerWeight := by
  intro s i hs
  rfl

/-- Coordinatewise addition preserves a common lower support bound. -/
lemma NTBelow.add
    {d inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {left right : CCExpans H inputWeight}
    (hleft : left.NTBelow lowerWeight)
    (hright : right.NTBelow lowerWeight) :
    (left.add right).NTBelow lowerWeight := by
  intro s i hs
  change (left.expansion s i).terms ++ (right.expansion s i).terms = []
  rw [hleft s i hs, hright s i hs]
  rfl

/-- Absence of lower coordinate terms implies the corresponding factor support bound. -/
lemma no_terms_below
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (hR : R.NTBelow lowerWeight) :
    SPFactora.WordWeightLeast lowerWeight
      (R.factors (n := n)) := by
  intro x hx
  rw [factors, prefixFactors] at hx
  rcases List.mem_flatMap.mp hx with ⟨j, _hj, hx⟩
  have hxweight := R.word_weight_factors hx
  rw [hxweight]
  by_contra hweight
  have hjlow : j + 1 < lowerWeight := Nat.lt_of_not_ge hweight
  rw [weightFactors] at hx
  rcases List.mem_flatMap.mp hx with ⟨i, _hi, hx⟩
  unfold BCExp.symbolicPowerFactors at hx
  rw [hR (j + 1) i hjlow] at hx
  change x ∈ ([] : List (SPFactora H inputWeight)) at hx
  exact List.not_mem_nil hx

end CCExpans

namespace SPFactora

/--
Normalize one symbolic factor semantically into one explicit expansion at a
selected Hall coordinate.
-/
noncomputable def normalCoordinateExpansion
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (x : SPFactora H inputWeight)
    (s : ℕ)
    (i : (H s).index) :
    BCExp inputWeight s :=
  if hweight : x.word.weight PEAddres.weight ≤ s then
    { terms :=
        [(hallCoordinate hn H hH (x.wordValue (n := n)) i * x.coefficient,
          x.recipe.weaken hweight)] }
  else
    BCExp.zero inputWeight s

/-- The selected semantic expansion has the expected scaled Hall coordinate. -/
lemma normal_coordinate_expansion
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (x : SPFactora H inputWeight)
    (q s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n)
    (i : (H s).index) :
    (x.normalCoordinateExpansion hn H hH s i).eval q =
      normalFormCoordinates hn H hH (x.wordValue (n := n)) s i *
        x.exponent q := by
  by_cases hweight : x.word.weight PEAddres.weight ≤ s
  · simp [normalCoordinateExpansion, hweight, hallCoordinate,
      BCExp.eval, BRTerm.eval, exponent]
    ring
  · have hzero :
        hallCoordinate hn H hH (x.wordValue (n := n)) i = 0 := by
      exact lower_central_series
        hn H hH (x.wordValue (n := n)) x.value_lower_series
          hs (Nat.lt_of_not_ge hweight) hsn i
    change
      normalFormCoordinates hn H hH (x.wordValue (n := n)) s i = 0 at hzero
    simp [normalCoordinateExpansion, hweight,
      BCExp.eval_zero, hzero]

/-- The semantic Hall-normal expansions of every coordinate of one factor. -/
noncomputable def normalCoordinateExpansions
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (x : SPFactora H inputWeight) :
    CCExpans H inputWeight where
  expansion := x.normalCoordinateExpansion hn H hH

/-- Evaluated semantic coordinates are integer-scaled Hall-normal coordinates. -/
lemma normal_coordinate_expansions
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (x : SPFactora H inputWeight)
    (q s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n) :
    (x.normalCoordinateExpansions hn H hH).eval q s =
      zscaledExponentFamily
        (normalFormCoordinates hn H hH (x.wordValue (n := n)))
        (x.exponent q) s := by
  funext i
  exact x.normal_coordinate_expansion hn H hH q s hs hsn i

/-- Hall-normal coordinates of a retained factor vanish below its word weight. -/
lemma coordinates_value_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (x : SPFactora H inputWeight)
    (hx : x.word.weight PEAddres.weight < n) :
    ∀ s, s < x.word.weight PEAddres.weight →
      normalFormCoordinates hn H hH (x.wordValue (n := n)) s = 0 := by
  intro s hs
  funext i
  by_cases hspos : 1 ≤ s
  · change hallCoordinate hn H hH (x.wordValue (n := n)) i = 0
    exact lower_central_series
      hn H hH (x.wordValue (n := n)) x.value_lower_series
        hspos hs (hs.trans hx) i
  · have hs0 : s = 0 := by omega
    subst s
    exact False.elim ((H 0).commutator i).weight_pos.false

/--
In the commutative high-weight region, the semantic normalized endpoint of
one retained factor evaluates to that factor.
-/
lemma list_coordinate_expansions
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (x : SPFactora H inputWeight)
    (hx : x.word.weight PEAddres.weight < n)
    (hcutoff : n ≤ 2 * x.word.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        ((x.normalCoordinateExpansions hn H hH).factors (n := n)) =
      x.eval (n := n) q := by
  rw [CCExpans.listEval_factors]
  calc
    collectedHallProduct (n := n) H
          ((x.normalCoordinateExpansions hn H hH).eval q) =
        collectedHallProduct (n := n) H
          (zscaledExponentFamily
            (normalFormCoordinates hn H hH (x.wordValue (n := n)))
            (x.exponent q)) := by
      unfold collectedHallProduct
      apply collected_product_coordinates
      intro s hs hsle
      exact x.normal_coordinate_expansions hn H hH q s hs (by omega)
    _ = collectedHallProduct (n := n) H
          (normalFormCoordinates hn H hH (x.wordValue (n := n))) ^
            x.exponent q := by
      exact zscaled_exponent_high
        hcutoff
        (normalFormCoordinates hn H hH (x.wordValue (n := n)))
        (x.coordinates_value_below hn H hH hx)
        (x.exponent q)
    _ = x.eval (n := n) q := by
      rw [collected_form_coordinates hn H hH]
      rfl

/-- Normalizing one sufficiently high factor introduces no lower terms. -/
lemma no_terms_expansions
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (x : SPFactora H inputWeight)
    (hx :
      lowerWeight ≤ x.word.weight PEAddres.weight) :
    (x.normalCoordinateExpansions hn H hH).NTBelow lowerWeight := by
  intro s i hs
  have hweight : ¬x.word.weight PEAddres.weight ≤ s := by
    omega
  simp [normalCoordinateExpansions, normalCoordinateExpansion, hweight,
    BCExp.zero]

end SPFactora

/-- Semantically normalize a finite list of high-weight symbolic factors. -/
noncomputable def coordinateExpansionsList
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) :
    List (SPFactora H inputWeight) →
      CCExpans H inputWeight
  | [] => CCExpans.zero H inputWeight
  | x :: xs =>
      (x.normalCoordinateExpansions hn H hH).add
        (coordinateExpansionsList hn H hH xs)

/-- A semantically normalized high-weight list introduces no lower terms. -/
lemma no_below_expansions
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (L : List (SPFactora H inputWeight))
    (hL : SPFactora.WordWeightLeast lowerWeight L) :
    (coordinateExpansionsList hn H hH L).NTBelow
      lowerWeight := by
  induction L with
  | nil =>
      exact CCExpans.no_below_zero H
  | cons x xs ih =>
      apply CCExpans.NTBelow.add
      · exact x.no_terms_expansions hn H hH
          (hL x (by simp))
      · exact ih fun y hy => hL y (by simp [hy])

/--
The normalized endpoint of a finite retained high-weight list evaluates to
the original factor list.
-/
lemma list_factors_expansions
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (L : List (SPFactora H inputWeight))
    (htruncated : SPFactora.IsTruncated n L)
    (hL : SPFactora.WordWeightLeast lowerWeight L)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        ((coordinateExpansionsList hn H hH L).factors (n := n)) =
      SPFactora.listEval (n := n) q L := by
  induction L with
  | nil =>
      have hfactors :
          ((CCExpans.zero H inputWeight).factors
            (n := n)) = [] := by
        unfold CCExpans.factors
          CCExpans.prefixFactors
        apply List.flatMap_eq_nil_iff.2
        intro s _hs
        unfold CCExpans.weightFactors
        apply List.flatMap_eq_nil_iff.2
        intro i _hi
        rfl
      rw [show coordinateExpansionsList hn H hH [] =
          CCExpans.zero H inputWeight by rfl,
        hfactors]
  | cons x xs ih =>
      let X := x.normalCoordinateExpansions hn H hH
      let R := coordinateExpansionsList hn H hH xs
      have hxhigh :
          lowerWeight ≤ x.word.weight PEAddres.weight :=
        hL x (by simp)
      have hxtruncated :
          x.word.weight PEAddres.weight < n :=
        htruncated x (by simp)
      have hxs :
          SPFactora.WordWeightLeast lowerWeight xs :=
        fun y hy => hL y (by simp [hy])
      have hxSupport :
          SPFactora.WordWeightLeast lowerWeight
            (X.factors (n := n)) :=
        CCExpans.no_terms_below
          X (x.no_terms_expansions hn H hH hxhigh)
      have hRSupport :
          SPFactora.WordWeightLeast lowerWeight
            (R.factors (n := n)) :=
        CCExpans.no_terms_below
          R (no_below_expansions hn H hH xs hxs)
      have hmerge :
          TSRwa (n := n)
            (X.factors (n := n) ++ R.factors (n := n))
            ((X.add R).factors (n := n)) := by
        apply
          CCExpans.factors_append_rewrites
        intro B hB A hA
        have hBhigh := hxSupport B hB
        have hAhigh := hRSupport A hA
        omega
      change
        SPFactora.listEval (n := n) q
            ((X.add R).factors (n := n)) =
          SPFactora.listEval (n := n) q (x :: xs)
      calc
        SPFactora.listEval (n := n) q
              ((X.add R).factors (n := n)) =
            SPFactora.listEval (n := n) q
              (X.factors (n := n) ++ R.factors (n := n)) :=
          hmerge.listEval_eq q
        _ = SPFactora.listEval (n := n) q
              (X.factors (n := n)) *
            SPFactora.listEval (n := n) q
              (R.factors (n := n)) := by
          rw [SPFactora.listEval_append]
        _ = x.eval (n := n) q *
            SPFactora.listEval (n := n) q xs := by
          rw [SPFactora.list_coordinate_expansions
            hn H hH x hxtruncated (by omega) q]
          exact congrArg (x.eval (n := n) q * ·)
            (ih (fun y hy => htruncated y (by simp [hy])) hxs)
        _ = SPFactora.listEval (n := n) q (x :: xs) := rfl

/-- Explicit semantic Hall-normal expansions for the retained class-two tail. -/
noncomputable def truncatedCollectedExpansions
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : HEFam H) :
    CCExpans H inputWeight :=
  coordinateExpansionsList hn H hH
    (truncatedCorrectionFactors
      (n := n) (inputWeight := inputWeight) e)

/-- The semantic normalized correction endpoint remains in doubled input weight. -/
lemma least_semantic_expansions
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : HEFam H) :
    SPFactora.WordWeightLeast (2 * inputWeight)
      ((truncatedCollectedExpansions
        (inputWeight := inputWeight) hn H hH e).factors (n := n)) := by
  apply
    CCExpans.no_terms_below
  exact no_below_expansions hn H hH _
    (least_truncated_factors e)

/-- Semantic normalization preserves the evaluation of the retained class-two tail. -/
lemma truncated_semantic_expansions
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        ((truncatedCollectedExpansions
          (inputWeight := inputWeight) hn H hH e).factors (n := n)) =
      SPFactora.listEval (n := n) q
        (truncatedCorrectionFactors
          (n := n) (inputWeight := inputWeight) e) := by
  exact list_factors_expansions
    hn H hH (lowerWeight := 2 * inputWeight) (by omega)
      (truncatedCorrectionFactors
        (n := n) (inputWeight := inputWeight) e)
      (SPFactora.isTruncated_truncate _)
      (least_truncated_factors e)
      q

/--
The full normalized class-two endpoint: scaled input coordinates plus the
semantic Hall-normal coordinates of the central correction tail.
-/
noncomputable def truncatedSemanticExpansions
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : HEFam H) :
    CCExpans H inputWeight :=
  (scaledCoordinateExpansions (inputWeight := inputWeight) e).add
    (truncatedCollectedExpansions
      (inputWeight := inputWeight) hn H hH e)

/-- The full semantic class-two endpoint evaluates to the powered Hall block. -/
lemma collected_semantic_expansions
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        ((truncatedSemanticExpansions
          (inputWeight := inputWeight) hn H hH e).factors (n := n)) =
      collectedHallProduct (n := n) H e ^ q := by
  let C :=
    truncatedCollectedExpansions
      (inputWeight := inputWeight) hn H hH e
  have hCsupport :
      SPFactora.WordWeightLeast (2 * inputWeight)
        (C.factors (n := n)) :=
    least_semantic_expansions
      hn H hH e
  have hmerge :
      TSRwa (n := n)
        ((scaledCoordinateExpansions
            (inputWeight := inputWeight) e).factors (n := n) ++
          C.factors (n := n))
        (((scaledCoordinateExpansions
            (inputWeight := inputWeight) e).add C).factors (n := n)) :=
    scaled_corrections_rewrites
      hcutoff e C hCsupport
  change
    SPFactora.listEval (n := n) q
        (((scaledCoordinateExpansions
          (inputWeight := inputWeight) e).add C).factors (n := n)) =
      collectedHallProduct (n := n) H e ^ q
  calc
    SPFactora.listEval (n := n) q
          (((scaledCoordinateExpansions
            (inputWeight := inputWeight) e).add C).factors (n := n)) =
        SPFactora.listEval (n := n) q
          ((scaledCoordinateExpansions
              (inputWeight := inputWeight) e).factors (n := n) ++
            C.factors (n := n)) :=
      hmerge.listEval_eq q
    _ = SPFactora.listEval (n := n) q
          ((scaledCoordinateExpansions
            (inputWeight := inputWeight) e).factors (n := n)) *
        SPFactora.listEval (n := n) q
          (C.factors (n := n)) := by
      rw [SPFactora.listEval_append]
    _ = SPFactora.listEval (n := n) q
          ((scaledCoordinateExpansions
            (inputWeight := inputWeight) e).factors (n := n)) *
        SPFactora.listEval (n := n) q
          (truncatedCorrectionFactors
            (n := n) (inputWeight := inputWeight) e) := by
      rw [truncated_semantic_expansions
        hn H hH hcutoff e q]
    _ = SPFactora.listEval (n := n) q
          ((scaledCoordinateExpansions
              (inputWeight := inputWeight) e).factors (n := n) ++
            truncatedCorrectionFactors
              (n := n) (inputWeight := inputWeight) e) := by
      rw [SPFactora.listEval_append]
    _ = SPFactora.listEval (n := n) q
          (truncatedCentralizedFactors
            (n := n) (inputWeight := inputWeight) e) := by
      rw [centralized_scaled_corrections]
    _ = collectedHallProduct (n := n) H e ^ q :=
      collected_centralized_factors
        hinputWeight hcutoff e heBelow q

/--
Any coordinate endpoint with the right evaluation identity supplies explicit
Claim 5 expansion data, even when the normalization proof is semantic rather
than an adjacent-swap rewrite run.
-/
theorem collected_expansion_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (R : CCExpans H inputWeight)
    (hR :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q (R.factors (n := n)) =
          collectedHallProduct (n := n) H e ^ q) :
    CEData (n := n) H e inputWeight := by
  intro _heBelow
  refine ⟨R.eval, ?_, ?_⟩
  · intro q
    exact (R.listEval_factors q).symm.trans (hR q)
  · intro s _hs _hsn i
    exact ⟨R.expansion s i, rfl⟩

/--
Semantic Hall-normal collection constructs the Claim 5 coordinate expansions
throughout the class-two range `n ≤ 3 * inputWeight`.
-/
theorem expansion_semantic_tail
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {e : HEFam H}
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    CEData (n := n) H e inputWeight := by
  apply collected_expansion_factors
    (truncatedSemanticExpansions
      (inputWeight := inputWeight) hn H hH e)
  exact collected_semantic_expansions
    hn H hH hinputWeight hcutoff e heBelow

/--
Semantic Hall-normal collection constructs the integer-valued coordinate
polynomials consumed directly by Claim 5 throughout the class-two range.
-/
theorem collected_semantic_tail
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {e : HEFam H}
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  CEData.toPolynomialData hinputWeight
    (expansion_semantic_tail
      hn H hH hinputWeight hcutoff heBelow)

end TCTex
end Towers

-- Merged from ClassTwoPositiveBelow.lean

/-!
# Positive-below adapter for class-two Hall-power collection

Claim 5 only requires positive Hall coordinates below the input weight to
vanish.  The explicit class-two source constructor asks for every coordinate
below that weight to vanish, including unused layers.  Normalizing those
irrelevant layers to zero does not change the collected Hall product.

This file records that adapter so the semantic class-two tail can be consumed
directly at the Claim 5 boundary.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace HEFam

/-- Replace all Hall-coordinate layers below `r` by zero. -/
def zeroBelow
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (r : ℕ) :
    HEFam H :=
  fun s => if s < r then 0 else e s

@[simp]
lemma zero_below
    {d r s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (e : HEFam H)
    (hs : s < r) :
    zeroBelow e r s = 0 := by
  simp [zeroBelow, hs]

@[simp]
lemma zero_below_self
    {d r s : ℕ}
    {H : ∀ t : ℕ, BCWta.{u} d t}
    (e : HEFam H)
    (hs : ¬s < r) :
    zeroBelow e r s = e s := by
  simp [zeroBelow, hs]

end HEFam

/--
Zeroing layers below `r` does not change the collected Hall product when its
visited positive layers below `r` were already zero.
-/
lemma collected_below_self
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow :
      ∀ s : ℕ,
        1 ≤ s →
          s < r →
            s < n →
              e s = 0) :
    collectedHallProduct (n := n) H (HEFam.zeroBelow e r) =
      collectedHallProduct (n := n) H e := by
  unfold collectedHallProduct
  apply collected_product_coordinates
  intro s hs hsn
  by_cases hsr : s < r
  · simp [HEFam.zeroBelow, hsr, heBelow s hs hsr (by omega)]
  · simp [HEFam.zeroBelow, hsr]

/--
The semantic class-two Hall-power tail satisfies Claim 5 under its native
positive-below premise.
-/
theorem
    collected_semantic_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {e : HEFam H} :
    CollectedPolynomialData
      (n := n) H e inputWeight := by
  intro heBelow
  let e' : HEFam H :=
    HEFam.zeroBelow e inputWeight
  have he'Below :
      ∀ s : ℕ, s < inputWeight → e' s = 0 := by
    intro s hs
    simp [e', hs]
  have he'Product :
      collectedHallProduct (n := n) H e' =
        collectedHallProduct (n := n) H e := by
    simpa [e'] using collected_below_self e heBelow
  rcases
      (collected_semantic_tail
        hn H hH hinputWeight hcutoff he'Below)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

end TCTex
end Towers
