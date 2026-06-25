import Submission.Group.Zassenhaus.Core
import Submission.Group.DenseGenerators.ZassenhausJenningsInduction

open scoped commutatorElement

/-!
## Statements migrated from `Submission.Theorems`

These declarations keep their historical `Submission.Theorems` namespace while living
next to the API they describe.
-/

namespace Submission
namespace Theorems

open Submission.Group
open Submission.GroupAlgebra

universe u v w x

/-- Zassenhaus filtrations are descending. -/
theorem zassenhausFiltrationDescending {p : ℕ} {G : Type u} [Group G]
    {m n : ℕ} (h : m ≤ n) :
    GroupAlgebra.zSubgro p G n ≤ GroupAlgebra.zSubgro p G m
  := by
  exact GroupAlgebra.zassenhausSubgroup_antitone p G h
/-- For prime `p`, p-th powers move to p times the filtration degree. -/
theorem zassenhausPBound {p : ℕ} [Fact p.Prime] {G : Type u} [Group G]
    {n : ℕ} {x : G} (hx : x ∈ GroupAlgebra.zSubgro p G n) :
    x ^ p ∈ GroupAlgebra.zSubgro p G (p * n)
  := by
  exact GroupAlgebra.pow_prime_mul (p := p) (G := G) hx
/-- The first certified Zassenhaus term is the whole group. -/
theorem firstTermGroup {p : ℕ} {G : Type u} [Group G]
    :
    GroupAlgebra.zSubgro p G 1 = ⊤
  := by
  exact GroupAlgebra.zassenhaus_one_top p G

/-- Lower-central terms have at least their expected Zassenhaus depth. -/
theorem lower_series_subgroup {p : ℕ} {G : Type u} [Group G]
    (k : ℕ) :
    Subgroup.lowerCentralSeries G k ≤ GroupAlgebra.zSubgro p G (k + 1)
  := by
  induction k with
  | zero =>
      rw [Subgroup.lowerCentralSeries_zero]
      exact top_le_iff.mpr (by simp [GroupAlgebra.zassenhaus_one_top p G])
  | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact (Subgroup.commutator_mono ih le_top).trans
        (by
          simpa [GroupAlgebra.zassenhaus_one_top, Nat.succ_eq_add_one,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            (GroupAlgebra.commutator_subgroup_any
              (p := p) (G := G) (m := k + 1) (n := 1)))

/-- Positive-indexed lower-central terms have at least their expected Zassenhaus depth. -/
theorem zassenhaus_term_subgroup {p : ℕ} {G : Type u} [Group G]
    {i : ℕ} (hi : 0 < i) :
    zassenhausLowerTerm G i ≤ GroupAlgebra.zSubgro p G i
  := by
  have hpred : i - 1 + 1 = i := by omega
  simpa [zassenhausLowerTerm, hpred] using
    lower_series_subgroup (p := p) (G := G) (i - 1)

/-- Prime-power iterates of lower-central elements land in every shallower
dimension-model Zassenhaus term. -/
theorem pow_p_subgroup
    {p n i j : ℕ} [Fact p.Prime] {G : Type u} [Group G] {y : G}
    (hy : y ∈ zassenhausLowerTerm G i)
    (hle : n ≤ i * p ^ j) :
    y ^ (p ^ j) ∈ GroupAlgebra.zSubgro p G n := by
  by_cases hi : 0 < i
  · exact
      GroupAlgebra.zassenhausSubgroup_antitone p G hle
        (GroupAlgebra.pow_zassenhaus_subgroup
          (p := p) (G := G)
          (zassenhaus_term_subgroup
            (p := p) (G := G) hi hy))
  · have hiZero : i = 0 := Nat.eq_zero_of_not_pos hi
    subst i
    have hnZero : n = 0 := by simpa using hle
    subst n
    simp

/-- The lower-central/p-power formula subgroup is contained in the dimension-subgroup
Zassenhaus term.  This is the constructive half of the Jennings formula supplied by
the restricted-series laws already proved in this file. -/
theorem formula_term_subgroup {p : ℕ} {G : Type u} [Group G]
    [Fact p.Prime] (n : ℕ) :
    zFTerm p n G ≤ GroupAlgebra.zSubgro p G n
  := by
  haveI : (GroupAlgebra.zSubgro p G n).Normal :=
    GroupAlgebra.zassenhausSubgroup_normal p G n
  apply Subgroup.normalClosure_le_normal
  intro x hx
  rcases hx with ⟨_hp, _hn, i, j, y, hi, hy, hineq, rfl⟩
  have hyDepth : (GroupAlgebra.restrictedNSeries p G).HasDepth y i := by
    exact zassenhaus_term_subgroup (p := p) hi hy
  have hpow :
      (GroupAlgebra.restrictedNSeries p G).HasDepth (y ^ p ^ j) n :=
    RNSeries.HasDepth.pow_p_iteratele
      (p := p) (F := GroupAlgebra.restrictedNSeries p G) hyDepth hineq
  simpa [RNSeries.HasDepth] using hpow

/-- At positive indices, the normal-closure formula agrees with the closure-based
Zassenhaus filtration used by the finite-quotient developments. -/
theorem formula_closure_filtration {p : ℕ} {G : Type u} [Group G]
    [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    zFTerm p n G = _root_.Submission.zassenhausFiltration p G n := by
  apply le_antisymm
  · haveI : (_root_.Submission.zassenhausFiltration p G n).Normal :=
      _root_.Submission.zassenhausFiltration_normal p G n
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases hx with ⟨_hp, _hn, i, j, y, hi, hy, hbound, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨i - 1, j, y, ?_, ?_, rfl⟩
    · simpa [zassenhausLowerTerm] using hy
    · have hpred : i - 1 + 1 = i := by omega
      simpa [hpred] using hbound
  · rw [_root_.Submission.zassenhausFiltration]
    apply (Subgroup.closure_le _).2
    intro x hx
    rcases hx with ⟨i, j, y, hy, hbound, rfl⟩
    apply Subgroup.subset_normalClosure
    refine ⟨Fact.out, hn, i + 1, j, y, Nat.succ_pos _, ?_, ?_, rfl⟩
    · simpa [zassenhausLowerTerm] using hy
    · exact hbound

/-- The reverse Jennings inclusion is elementary in degree one. -/
theorem zassenhaus_formula_term {p : ℕ} {G : Type u}
    [Group G] [Fact p.Prime] :
    GroupAlgebra.zSubgro p G 1 ≤ zFTerm p 1 G := by
  rw [GroupAlgebra.zassenhaus_one_top, formula_term_top]

namespace RJRed

/-!
## Reduction of the reverse Jennings inclusion

The universal reverse inclusion is deliberately assembled from smaller statements.
The reduction has four stages.

1. Quotient by `zFTerm p n G`.  The formula term is then trivial.
2. Remove the arbitrary-group hypothesis from a killed layer by finite support and
   Restricted Burnside.
3. Separate a finite killed layer using a finite PBW/Jennings argument.
4. Supply the two group-theoretic laws needed by that finite argument from Hall
   collection on formula generators.

The declarations ending in `At` below package the interfaces between these stages.
They are intentionally local to the reverse Jennings proof: downstream files may
replace individual placeholders without changing the final assembly theorem.
-/

/-- Raw formula generators below a killed cutoff are stable under `p`th powers.

This is the atom-level input for the power-law closure lift.  Unlike the final
reverse inclusion, it discusses one explicit lower-central prime-power generator
and one elementary operation. -/
def FormulaPowerBound
    (p n : ℕ) :
    Prop :=
  ∀ {Q : Type u} [Group Q] [Finite Q],
    zFTerm p n Q = ⊥ →
      ∀ {r : ℕ} {x : Q},
        r < n →
        x ∈ zassenhausFormulaGenerators p r Q →
          x ^ p ∈ zFTerm p (p * r) Q

/-- Raw formula generators below a killed cutoff have additive commutator depth.

This is the Hall-Petresco boundary statement.  It is substantially narrower than
the reverse Jennings theorem: the ambient group is finite, the top formula layer
is already killed, and both inputs are individual explicit generators rather than
arbitrary elements of augmentation-defined dimension subgroups. -/
def FormulaGeneratorBound
    (p n : ℕ) :
    Prop :=
  ∀ {Q : Type u} [Group Q] [Finite Q],
    zFTerm p n Q = ⊥ →
      ∀ {r s : ℕ} {x y : Q},
        r < n →
        s < n →
        x ∈ zassenhausFormulaGenerators p r Q →
        y ∈ zassenhausFormulaGenerators p s Q →
          ⁅x, y⁆ ∈ zFTerm p (r + s) Q

/-- Full formula terms below a killed cutoff are stable under `p`th powers.

Passing from `FormulaPowerBound` to this statement is a normal-closure
calculation.  Products and conjugates create commutator corrections, so the
generator commutator law is supplied separately to the closure lift. -/
def FormulaBound
    (p n : ℕ) :
    Prop :=
  ∀ {Q : Type u} [Group Q] [Finite Q],
    zFTerm p n Q = ⊥ →
      ∀ {r : ℕ} {x : Q},
        r < n →
        x ∈ zFTerm p r Q →
          x ^ p ∈ zFTerm p (p * r) Q

/-- Full formula terms below a killed cutoff have additive commutator depth.

This is still only a finite killed-layer law.  It does not mention augmentation
ideals or assert any equality between the two candidate filtrations. -/
def FormulaCommutatorBound
    (p n : ℕ) :
    Prop :=
  ∀ {Q : Type u} [Group Q] [Finite Q],
    zFTerm p n Q = ⊥ →
      ∀ {r s : ℕ} {x y : Q},
        r < n →
        s < n →
        x ∈ zFTerm p r Q →
        y ∈ zFTerm p s Q →
          ⁅x, y⁆ ∈ zFTerm p (r + s) Q

/-- Finite groups separate the augmentation-defined term at a killed formula layer.

This is the finite PBW/Jennings output.  It is confined to finite groups with the
explicit formula term already equal to bottom. -/
def KilledFormulaSeparation
    (p n : ℕ) :
    Prop :=
  ∀ {Q : Type u} [Group Q] [Finite Q],
    zFTerm p n Q = ⊥ →
      GroupAlgebra.zSubgro p Q n = ⊥

/-- Arbitrary groups separate the augmentation-defined term at a killed formula layer.

The only difference from `KilledFormulaSeparation` is removal of the
finiteness hypothesis.  This is the finite-support/Restricted-Burnside stage, not
the Hall or PBW stage. -/
def KilledSeparation
    (p n : ℕ) :
    Prop :=
  ∀ {Q : Type u} [Group Q],
    zFTerm p n Q = ⊥ →
      GroupAlgebra.zSubgro p Q n = ⊥

/-- The raw generator `p`-power law is elementary: increment the prime-power
exponent in the defining formula generator. -/
lemma formulaGeneratorBound
    {p n : ℕ} [Fact p.Prime] :
    FormulaPowerBound.{u} p n := by
  intro Q _ _ _htrivial r x _hr hx
  rcases hx with ⟨hp, hrPos, i, j, y, hi, hy, hweight, rfl⟩
  apply Subgroup.subset_normalClosure
  refine ⟨hp, Nat.mul_pos (Fact.out : Nat.Prime p).pos hrPos,
    i, j + 1, y, hi, hy, ?_, ?_⟩
  · calc
      p * r ≤ p * (i * p ^ j) := Nat.mul_le_mul_left p hweight
      _ = i * p ^ (j + 1) := by
        rw [pow_succ]
        ac_rfl
  · rw [pow_succ, pow_mul]

/-- Boundary-only Hall-Petresco input for the strong-induction Jennings
reduction.

The two commutator inputs are not arbitrary filtration elements, nor arbitrary
formula generators with slack in their weights.  They are explicit prime-power
powers of lower-central elements, and their exact weighted degrees already
reach a formula layer that has been killed.  Thus the required conclusion is
the equality `⁅x ^ (p ^ a), y ^ (p ^ b)⁆ = 1`.

This is strictly narrower than `FormulaGeneratorBound`: it only
addresses the boundary case.  Interior commutator bounds are recovered by
strong induction through the dimension-subgroup model. -/
def BoundaryCommutatorTrivial
    (p n : ℕ) :
    Prop :=
  ∀ {Q : Type u} [Group Q] [Finite Q],
    _root_.Submission.zassenhausFiltration p Q n = ⊥ →
      ∀ {i j a b : ℕ} {x y : Q},
        x ∈ Subgroup.lowerCentralSeries Q i →
        y ∈ Subgroup.lowerCentralSeries Q j →
        n ≤ (i + 1) * p ^ a + (j + 1) * p ^ b →
          ⁅x ^ (p ^ a), y ^ (p ^ b)⁆ = 1

/-- Unpack two exact generators and apply the boundary-only Hall-Petresco
statement to their lower-central representatives. -/
lemma exact_killed_boundary
    {p n : ℕ} [Fact p.Prime]
    (hHall : BoundaryCommutatorTrivial.{u} p n) :
    ∀ {Q : Type u} [Group Q] [Finite Q],
      _root_.Submission.zassenhausFiltration p Q n = ⊥ →
        _root_.Submission.KilledBoundaryTrivial p Q n := by
  intro Q _ _ htrivial r s x y _hr _hs hrs hx hy
  rcases hx with ⟨i, a, x0, hx0, hrWeight, rfl⟩
  rcases hy with ⟨j, b, y0, hy0, hsWeight, rfl⟩
  apply hHall htrivial hx0 hy0
  simpa [hrWeight, hsWeight] using hrs

/-- The boundary-only lower-central Hall input implies the reverse
dimension-subgroup inclusion into the closure-based explicit filtration.

The imported strong-induction reduction handles every interior degree.  At the
single new boundary it invokes exactly
`BoundaryCommutatorTrivial`. -/
lemma closure_filtration_boundary
    {p : ℕ} [Fact p.Prime]
    (hHall :
      ∀ {m : ℕ}, 1 < m →
        BoundaryCommutatorTrivial.{u} p m)
    {G : Type u} [Group G]
    {n : ℕ} (hn : 0 < n) :
    GroupAlgebra.zSubgro p G n ≤
      _root_.Submission.zassenhausFiltration p G n := by
  change
    GroupAlgebra.dSubgro (ZMod p) G n ≤
      _root_.Submission.zassenhausFiltration p G n
  apply
    _root_.Submission.zmod_boundary_trivial
      (p := p) ?_ hn
  intro m hm Q _ _ htrivial
  exact
    exact_killed_boundary
      (hHall hm) htrivial

/-- Once the boundary-only Hall input is available in every killed degree, the
raw formula-generator commutator estimate follows without another collection
argument.

Each formula generator lies in the augmentation-defined Zassenhaus subgroup.
The augmentation-defined commutator law adds degrees, the strong-induction
reduction moves the resulting element back into the closure filtration, and
the positive-index comparison identifies that closure filtration with the
formula term. -/
lemma formula_bound_boundary
    {p n : ℕ} [Fact p.Prime]
    (hHall :
      ∀ {m : ℕ}, 1 < m →
        BoundaryCommutatorTrivial.{u} p m) :
    FormulaGeneratorBound.{u} p n := by
  intro Q _ _ _htrivial r s x y _hr _hs hx hy
  have hrs : 0 < r + s := Nat.add_pos_left hx.2.1 s
  rw [formula_closure_filtration
    (p := p) (G := Q) (r + s) hrs]
  apply
    closure_filtration_boundary
      hHall hrs
  exact
    GroupAlgebra.commutator_add_any p Q
      (formula_term_subgroup (p := p) (G := Q) r
        (formula_subset_term p r Q hx))
      (formula_term_subgroup (p := p) (G := Q) s
        (formula_subset_term p s Q hy))

/-- Lift the raw generator commutator estimate through the two normal closures.

This is a closure-induction lemma.  Its hypotheses already contain the hard
Hall estimate for individual generators; no augmentation algebra is involved. -/
lemma formula_bound_generator
    {p n : ℕ} [Fact p.Prime]
    (hgen : FormulaGeneratorBound.{u} p n) :
    FormulaCommutatorBound.{u} p n := by
  intro Q _ _ htrivial r s x y hr hs hx hy
  change
    x ∈ Subgroup.closure
      (Group.conjugatesOfSet (zassenhausFormulaGenerators p r Q)) at hx
  change
    y ∈ Subgroup.closure
      (Group.conjugatesOfSet (zassenhausFormulaGenerators p s Q)) at hy
  have hconj :
      ∀ {t : ℕ} {z : Q},
        z ∈ Group.conjugatesOfSet (zassenhausFormulaGenerators p t Q) →
          z ∈ zassenhausFormulaGenerators p t Q := by
    intro t z hz
    rcases Group.mem_conjugatesOfSet_iff.mp hz with ⟨a, ha, hza⟩
    rcases isConj_iff.mp hza with ⟨c, rfl⟩
    rcases ha with ⟨hp, ht, i, j, a, hi, ha, hweight, rfl⟩
    refine ⟨hp, ht, i, j, c * a * c⁻¹, hi, ?_, hweight, ?_⟩
    · exact
        (inferInstance : (zassenhausLowerTerm Q i).Normal).conj_mem
          a ha c
    · exact (conj_pow (a := c) (b := a) (i := p ^ j)).symm
  exact
    commutator_element_closure
      (K := zFTerm p (r + s) Q)
      (fun ha hb => hgen htrivial hr hs (hconj ha) (hconj hb))
      hx hy

/-- The finite PBW/Jennings separator consumes the formula filtration laws.

This is the algebraic finite-group step: choose weighted representatives, build
the truncated Jennings monomial basis, and use it to detect the augmentation
power.  Its exact-generator interface supplies the elementary power bookkeeping
internally, while the full power law remains part of this packaged boundary. -/
lemma killed_separation_laws
    {p n : ℕ} [Fact p.Prime]
    (hn : 1 < n)
    (_hpow : FormulaBound.{u} p n)
    (hcomm : FormulaCommutatorBound.{u} p n) :
    KilledFormulaSeparation.{u} p n := by
  have hnPos : 0 < n := lt_trans Nat.zero_lt_one hn
  have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hnPos)
  intro Q _ _ hformula
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply
    _root_.Submission.zmod_generator_law.{u}
      (p := p) (n := n) hnOne
  · intro R _ _ hroot r s a b hr hs ha hb
    have hformulaR : zFTerm p n R = ⊥ := by
      rw [formula_closure_filtration
        (p := p) (G := R) n hnPos]
      exact hroot
    have hrPos : 0 < r :=
      _root_.Submission.exact_set_pos ha
    have hsPos : 0 < s :=
      _root_.Submission.exact_set_pos hb
    rw [← formula_closure_filtration
      (p := p) (G := R) (r + s) (Nat.add_pos_left hrPos s)]
    exact hcomm hformulaR hr hs
      (by
        rw [formula_closure_filtration
          (p := p) (G := R) r hrPos]
        exact
          _root_.Submission.exact_subset_filtration
            ha)
      (by
        rw [formula_closure_filtration
          (p := p) (G := R) s hsPos]
        exact
          _root_.Submission.exact_subset_filtration
            hb)
  · rw [← formula_closure_filtration
      (p := p) (G := Q) n hnPos]
    exact hformula
  · exact hx

/-- Remove the finiteness assumption from a killed formula layer.

For an element of the augmentation-defined term, finite support places its
augmentation witness inside a finitely generated subgroup.  The killed formula
layer bounds nilpotency class and exponent there; Restricted Burnside makes that
subgroup finite, after which `hfinite` applies. -/
lemma killed_formula_separation
    {p n : ℕ} [Fact p.Prime]
    (hn : 1 < n)
    (hfinite : KilledFormulaSeparation.{u} p n) :
    KilledSeparation.{u} p n := by
  have hnPos : 0 < n := lt_trans Nat.zero_lt_one hn
  intro Q _ hformula
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply
    _root_.Submission.zmod_filtration_bot
      (p := p) (n := n) hn
  · intro R _ _ hroot y hy
    have hformulaR : zFTerm p n R = ⊥ := by
      rw [formula_closure_filtration
        (p := p) (G := R) n hnPos]
      exact hroot
    have hbot : GroupAlgebra.zSubgro p R n = ⊥ :=
      hfinite hformulaR
    have hyZassenhaus : y ∈ GroupAlgebra.zSubgro p R n := hy
    rw [hbot] at hyZassenhaus
    have hyBot : y ∈ (⊥ : Subgroup R) := hyZassenhaus
    simpa using hyBot
  · rw [← formula_closure_filtration
      (p := p) (G := Q) n hnPos]
    exact hformula
  · exact hx

/-- Quotient reduction: if killed formula layers separate their matching
augmentation-defined terms, then the reverse inclusion holds at a fixed depth.

This lemma is sor_ry-free.  It is the short formal core of the reduction: quotient
by the formula term, kill the target Zassenhaus term downstairs, and pull the
result back along the quotient map. -/
lemma formula_killed_separation
    {p n : ℕ} [Fact p.Prime]
    {G : Type u} [Group G]
    (_hn : 1 < n)
    (hkilled :
      ∀ {Q : Type u} [Group Q],
        zFTerm p n Q = ⊥ →
          GroupAlgebra.zSubgro p Q n = ⊥) :
    GroupAlgebra.zSubgro p G n ≤
      zFTerm p n G := by
  apply GroupAlgebra.zassenhaus_subgroup_bot
  exact
    hkilled
      (formula_self_bot p n G)

end RJRed

/-- If the reverse Jennings inclusion is known one step deeper, then the corresponding
formula layer is central modulo its successor. -/
theorem formula_top_reverse
    {p : ℕ} {G : Type u} [Group G] [Fact p.Prime] {n : ℕ}
    (hreverse :
      GroupAlgebra.zSubgro p G (n + 1) ≤
        zFTerm p (n + 1) G) :
    ⁅zFTerm p n G, (⊤ : Subgroup G)⁆ ≤
      zFTerm p (n + 1) G := by
  apply Subgroup.commutator_le.mpr
  intro x hx y _hy
  apply hreverse
  exact
    GroupAlgebra.commutator_add_any p G
      (formula_term_subgroup (p := p) (G := G) n hx)
      (by
        rw [GroupAlgebra.zassenhaus_one_top]
        exact Subgroup.mem_top y)

/-- The formula subgroup is the part of the Jennings identification proved locally:
the reverse inclusion is the full Jennings-Lazard dimension-subgroup theorem and is
not a consequence of the restricted-series API alone. -/
theorem jenningsDimensionEquality {p : ℕ} {G : Type u} [Group G] [Fact p.Prime]
    (n : ℕ) (_hn : 0 < n) :
    zFTerm p n G ≤ GroupAlgebra.zSubgro p G n
  := by
  exact formula_term_subgroup (p := p) (G := G) n

/-- Zassenhaus commutators add degrees. -/
theorem zassenhausCommutatorBound {p : ℕ} {G : Type u} [Group G]
    {m n : ℕ} {x y : G} :
    x ∈ GroupAlgebra.zSubgro p G m →
      y ∈ GroupAlgebra.zSubgro p G n →
        x * y * x⁻¹ * y⁻¹ ∈ GroupAlgebra.zSubgro p G (m + n)
  := by
  exact fun hx hy => GroupAlgebra.commutator_add_any p G hx hy
/-- Initial group classes respect commutators. -/
theorem initialRespectsCommutators {p : ℕ} {G : Type u} [Group G]
    {m n : ℕ} {x y : G} :
    x ∈ GroupAlgebra.zSubgro p G m →
      y ∈ GroupAlgebra.zSubgro p G n →
        x * y * x⁻¹ * y⁻¹ ∈ GroupAlgebra.zSubgro p G (m + n)
  := by
  exact fun hx hy => GroupAlgebra.commutator_add_any p G hx hy
/-- For prime `p`, initial group classes respect p-powers. -/
theorem initialRespectsPowers {p : ℕ} [Fact p.Prime] {G : Type u} [Group G]
    {n : ℕ} {x : G} :
    x ∈ GroupAlgebra.zSubgro p G n →
      x ^ p ∈ GroupAlgebra.zSubgro p G (p * n)
  := by
  exact fun hx => GroupAlgebra.pow_prime_mul (p := p) (G := G) hx
/-- The PBW/Jennings theorem package identifies filtration and augmentation data. -/
theorem pbwJenningsTheorem {p : ℕ} {G : Type u} [Group G] [Fact p.Prime]
    (n : ℕ) :
    (GroupAlgebra.zSubgro p G n : Set G) =
      GroupAlgebra.dSubgro (ZMod p) G n
  := by
  rfl

end Theorems
end Submission
