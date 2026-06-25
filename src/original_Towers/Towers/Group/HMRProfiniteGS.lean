import Towers.Group.ProCompletedFox

/-!
# Reusable Golod--Shafarevich infrastructure for HMR cutting

The arithmetic input to an HMR cutting argument is a Shafarevich relation
bound.  Under a temporary finiteness assumption on a cut quotient, it gives a
finite filtered presentation whose relators can be injected into two explicit
families:

* at most `d` arithmetic relators, each of depth at least `2`;
* at most one cut relator at each index `i`, of depth at least `k + i`.

This file proves everything after that input: the geometric tail estimate, the
weighted relator estimate, the negative rational GS evaluation, and the
infinitude contradiction.
-/

open scoped BigOperators

noncomputable section

namespace Towers
namespace HPGs

universe u

/-- The quadratic GS upper bound supplied by `r ≤ d`. -/
def quadraticGSValue (d : ℕ) (t : ℚ) : ℚ :=
  1 - d * t + d * t ^ 2

/-- Numerical strict Golod--Shafarevich data before adding the HMR cut relators. -/
structure StrictGSParameters (d : ℕ) where
  t0 : ℚ
  ε : ℚ
  t0_pos : 0 < t0
  t_0_one : t0 < 1
  ε_pos : 0 < ε
  base_deficit : quadraticGSValue d t0 ≤ -ε

/-- The geometric tail bound required at an HMR cutting level. -/
def CuttingTailBound {d : ℕ} (c : StrictGSParameters d) (k : ℕ) : Prop :=
  c.t0 ^ k / (1 - c.t0) < c.ε

/-- The denominator in the HMR tail bound is positive. -/
theorem tail_denominator_pos {d : ℕ} (c : StrictGSParameters d) :
    0 < 1 - c.t0 := by
  linarith [c.t_0_one]

/-- A finite selection of HMR cut weights is bounded by the full geometric tail. -/
theorem cut_sum_tail
    {d : ℕ} (c : StrictGSParameters d) (k : ℕ) (s : Finset ℕ) :
    (∑ i ∈ s, c.t0 ^ (k + i)) ≤ c.t0 ^ k / (1 - c.t0) := by
  have ht0_nonneg_real : 0 ≤ (c.t0 : ℝ) := by
    exact_mod_cast c.t0_pos.le
  have ht0_lt_one_real : (c.t0 : ℝ) < 1 := by
    exact_mod_cast c.t_0_one
  have hgeom : Summable (fun i : ℕ => (c.t0 : ℝ) ^ i) :=
    summable_geometric_of_lt_one ht0_nonneg_real ht0_lt_one_real
  have hshift : Summable (fun i : ℕ => (c.t0 : ℝ) ^ (k + i)) := by
    simpa [pow_add] using hgeom.mul_left ((c.t0 : ℝ) ^ k)
  have hreal :
      (∑ i ∈ s, (c.t0 : ℝ) ^ (k + i)) ≤
        (c.t0 : ℝ) ^ k / (1 - (c.t0 : ℝ)) := by
    calc
      (∑ i ∈ s, (c.t0 : ℝ) ^ (k + i)) ≤ ∑' i : ℕ, (c.t0 : ℝ) ^ (k + i) :=
        hshift.sum_le_tsum s (fun i _ => pow_nonneg ht0_nonneg_real (k + i))
      _ = (c.t0 : ℝ) ^ k * ∑' i : ℕ, (c.t0 : ℝ) ^ i := by
        simp_rw [pow_add]
        exact tsum_mul_left
      _ = (c.t0 : ℝ) ^ k * (1 - (c.t0 : ℝ))⁻¹ := by
        rw [tsum_geometric_of_lt_one ht0_nonneg_real ht0_lt_one_real]
      _ = (c.t0 : ℝ) ^ k / (1 - (c.t0 : ℝ)) := by
        rw [div_eq_mul_inv]
  exact_mod_cast hreal

/-- A sufficiently small HMR tail preserves negativity of the quadratic GS bound. -/
theorem quadratic_tail_neg
    {d : ℕ} (c : StrictGSParameters d) {k : ℕ}
    (hk : CuttingTailBound c k) :
    quadraticGSValue d c.t0 + c.t0 ^ k / (1 - c.t0) < 0 := by
  dsimp [CuttingTailBound] at hk
  linarith [c.base_deficit]

/--
The explicit output of a Shafarevich relation bound for a finite HMR cut
quotient.  The injection records, without a certificate factory or a hidden GS
conclusion, that each relator is either one of at most `d` arithmetic relators
or the unique selected cut relator at an index `i`.
-/
structure FSBound
    (p d k : ℕ) (Q : Type u) [Group Q] where
  fp : FPres.{u} p
  [fact_prime : Fact p.Prime]
  [finite_gen : Finite fp.Gen]
  [fintype_relator : Fintype fp.toPresentation.Relator]
  groupEquiv : fp.Group ≃* Q
  generatorCount_eq : fp.generatorCount = d
  relatorCode : fp.toPresentation.Relator ↪ (Fin d ⊕ ℕ)
  depth_ge : ∀ r,
    match relatorCode r with
    | Sum.inl _ => 2 ≤ fp.depths.depth r
    | Sum.inr i => k + i ≤ fp.depths.depth r

/-- The relators coded as arithmetic Shafarevich relators. -/
noncomputable def FSBound.arithmeticRelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) :
    Finset S.fp.toPresentation.Relator :=
  by
    classical
    letI : Fintype S.fp.toPresentation.Relator := S.fintype_relator
    exact Finset.univ.filter fun r =>
      match S.relatorCode r with
      | Sum.inl _ => True
      | Sum.inr _ => False

/-- The relators coded as selected HMR cut relators. -/
noncomputable def FSBound.cutRelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) :
    Finset S.fp.toPresentation.Relator :=
  by
    classical
    letI : Fintype S.fp.toPresentation.Relator := S.fintype_relator
    exact Finset.univ.filter fun r =>
      match S.relatorCode r with
      | Sum.inl _ => False
      | Sum.inr _ => True

/-- The index of a selected cut relator. -/
def FSBound.cutIndex
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q)
    (r : S.fp.toPresentation.Relator) : ℕ :=
  match S.relatorCode r with
  | Sum.inl _ => 0
  | Sum.inr i => i

theorem FSBound.mem_arith_relatorsiff
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) (r : S.fp.toPresentation.Relator) :
    r ∈ S.arithmeticRelators ↔ ∃ j, S.relatorCode r = Sum.inl j := by
  classical
  letI : Fintype S.fp.toPresentation.Relator := S.fintype_relator
  cases h : S.relatorCode r with
  | inl j => simp [arithmeticRelators, h]
  | inr i => simp [arithmeticRelators, h]

theorem FSBound.mem_cut_relatorsiff
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) (r : S.fp.toPresentation.Relator) :
    r ∈ S.cutRelators ↔ ∃ i, S.relatorCode r = Sum.inr i := by
  classical
  letI : Fintype S.fp.toPresentation.Relator := S.fintype_relator
  cases h : S.relatorCode r with
  | inl j => simp [cutRelators, h]
  | inr i => simp [cutRelators, h]

noncomputable def FSBound.arithmeticIndex
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) (r : S.arithmeticRelators) : Fin d :=
  Classical.choose ((S.mem_arith_relatorsiff r.1).mp r.2)

theorem FSBound.relator_code_arithindex
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) (r : S.arithmeticRelators) :
    S.relatorCode r.1 = Sum.inl (S.arithmeticIndex r) :=
  Classical.choose_spec ((S.mem_arith_relatorsiff r.1).mp r.2)

theorem FSBound.relator_code_cutindex
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) (r : S.fp.toPresentation.Relator)
    (hr : r ∈ S.cutRelators) :
    S.relatorCode r = Sum.inr (S.cutIndex r) := by
  rcases (S.mem_cut_relatorsiff r).mp hr with ⟨i, hi⟩
  simp [cutIndex, hi]

theorem FSBound.arith_relatordisjoin_cutrelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) :
    Disjoint S.arithmeticRelators S.cutRelators := by
  classical
  rw [Finset.disjoint_left]
  intro r harith hcut
  rcases (S.mem_arith_relatorsiff r).mp harith with ⟨j, hj⟩
  rcases (S.mem_cut_relatorsiff r).mp hcut with ⟨i, hi⟩
  rw [hj] at hi
  cases hi

theorem FSBound.memarith_relatorsor_memcutrelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) (r : S.fp.toPresentation.Relator) :
    r ∈ S.arithmeticRelators ∨ r ∈ S.cutRelators := by
  classical
  cases h : S.relatorCode r with
  | inl j =>
      exact Or.inl ((S.mem_arith_relatorsiff r).2 ⟨j, h⟩)
  | inr i =>
      exact Or.inr ((S.mem_cut_relatorsiff r).2 ⟨i, h⟩)

theorem FSBound.arith_relators_cardle
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) :
    S.arithmeticRelators.card ≤ d := by
  classical
  let code : S.arithmeticRelators → Fin d := fun r => S.arithmeticIndex r
  have hcode : Function.Injective code := by
    intro r s hrs
    apply Subtype.ext
    apply S.relatorCode.injective
    change S.arithmeticIndex r = S.arithmeticIndex s at hrs
    rw [S.relator_code_arithindex, S.relator_code_arithindex, hrs]
  calc
    S.arithmeticRelators.card = Fintype.card S.arithmeticRelators := by simp
    _ ≤ Fintype.card (Fin d) := Fintype.card_le_of_injective code hcode
    _ = d := Fintype.card_fin d

theorem FSBound.cut_indexinj_cutrelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) :
    Set.InjOn S.cutIndex S.cutRelators := by
  intro r hr s hs hrs
  apply S.relatorCode.injective
  rw [S.relator_code_cutindex r hr, S.relator_code_cutindex s hs, hrs]

theorem FSBound.arithmetic_depth_ge
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) (r : S.fp.toPresentation.Relator)
    (hr : r ∈ S.arithmeticRelators) :
    2 ≤ S.fp.depths.depth r := by
  rcases (S.mem_arith_relatorsiff r).mp hr with ⟨j, hj⟩
  simpa [hj] using S.depth_ge r

theorem FSBound.cut_depth_ge
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q) (r : S.fp.toPresentation.Relator)
    (hr : r ∈ S.cutRelators) :
    k + S.cutIndex r ≤ S.fp.depths.depth r := by
  simpa [S.relator_code_cutindex r hr] using S.depth_ge r

theorem FSBound.arith_weight_sumle
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q)
    {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ r ∈ S.arithmeticRelators, t ^ S.fp.depths.depth r) ≤ d * t ^ 2 := by
  calc
    (∑ r ∈ S.arithmeticRelators, t ^ S.fp.depths.depth r) ≤
        ∑ _r ∈ S.arithmeticRelators, t ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      apply pow_le_pow_of_le_one ht0 ht1
      exact S.arithmetic_depth_ge r hr
    _ = S.arithmeticRelators.card * t ^ 2 := by simp
    _ ≤ d * t ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast S.arith_relators_cardle) (pow_nonneg ht0 2)

theorem FSBound.cut_weightsum_letail
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q)
    (c : StrictGSParameters d) :
    (∑ r ∈ S.cutRelators, c.t0 ^ S.fp.depths.depth r) ≤
      c.t0 ^ k / (1 - c.t0) := by
  calc
    (∑ r ∈ S.cutRelators, c.t0 ^ S.fp.depths.depth r) ≤
        ∑ r ∈ S.cutRelators, c.t0 ^ (k + S.cutIndex r) := by
      apply Finset.sum_le_sum
      intro r hr
      apply pow_le_pow_of_le_one c.t0_pos.le c.t_0_one.le
      exact S.cut_depth_ge r hr
    _ = ∑ i ∈ S.cutRelators.image S.cutIndex, c.t0 ^ (k + i) := by
      rw [Finset.sum_image S.cut_indexinj_cutrelators]
    _ ≤ c.t0 ^ k / (1 - c.t0) :=
      cut_sum_tail c k (S.cutRelators.image S.cutIndex)

theorem FSBound.relator_weightsum_letail
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q)
    [Fintype S.fp.toPresentation.Relator]
    (c : StrictGSParameters d) :
    (∑ r : S.fp.toPresentation.Relator, c.t0 ^ S.fp.depths.depth r) ≤
      d * c.t0 ^ 2 + c.t0 ^ k / (1 - c.t0) := by
  classical
  have hunion : S.arithmeticRelators ∪ S.cutRelators = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro r
    rcases S.memarith_relatorsor_memcutrelators r with harith | hcut
    · exact Finset.mem_union_left _ harith
    · exact Finset.mem_union_right _ hcut
  rw [← hunion, Finset.sum_union S.arith_relatordisjoin_cutrelators]
  exact add_le_add
    (S.arith_weight_sumle c.t0_pos.le c.t_0_one.le)
    (S.cut_weightsum_letail c)

/-- The rational GS polynomial is the base term plus the weighted relator sum. -/
theorem gs_rat_sum
    {p : ℕ} (FP : FPres p)
    [Fintype FP.toPresentation.Relator] (t : ℚ) :
    FP.gsEvalRat t =
      1 - FP.generatorCount * t +
        ∑ r : FP.toPresentation.Relator, t ^ FP.depths.depth r := by
  classical
  let M := FP.maxRelatorDepth
  have hhist :
      (∑ q ∈ Finset.range (M + 2), (FP.relatorDepthMultiplicity q : ℚ) * t ^ q) =
        ∑ r : FP.toPresentation.Relator, t ^ FP.depths.depth r := by
    have hlast : FP.relatorDepthMultiplicity (M + 1) = 0 := by
      exact FP.relator_multiplicity_max (by dsimp [M]; omega)
    rw [show M + 2 = (M + 1) + 1 by omega, Finset.sum_range_succ, hlast]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    let s : Finset FP.toPresentation.Relator := Finset.univ
    let u : Finset ℕ := Finset.range (M + 1)
    have hmap : ∀ r ∈ s, FP.depths.depth r ∈ u := by
      intro r _hr
      simp only [u, Finset.mem_range]
      exact Nat.lt_succ_of_le (FP.depth_max_relator r)
    have hfiber := Finset.sum_fiberwise_of_maps_to (s := s) (t := u)
      (g := fun r : FP.toPresentation.Relator => FP.depths.depth r) hmap
      (f := fun r : FP.toPresentation.Relator => t ^ FP.depths.depth r)
    rw [← hfiber]
    apply Finset.sum_congr rfl
    intro q hq
    calc
      (FP.relatorDepthMultiplicity q : ℚ) * t ^ q =
          ∑ r ∈ s with FP.depths.depth r = q, t ^ q := by
            simp [FPres.relatorDepthMultiplicity, s]
      _ = ∑ r ∈ s with FP.depths.depth r = q, t ^ FP.depths.depth r := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [(Finset.mem_filter.mp hr).2]
  unfold FPres.gsEvalRat FPres.gsCoeffInt
  simp_rw [Int.cast_add, Int.cast_natCast, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hhist]
  simp [FPres.deltaCoeff]
  ring

/-- The explicit relation bound and the geometric tail give a negative GS evaluation. -/
theorem FSBound.gs_polyeval_ratneg
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q)
    [Fintype S.fp.toPresentation.Relator]
    (c : StrictGSParameters d)
    (hk : CuttingTailBound c k) :
    S.fp.gsEvalRat c.t0 < 0 := by
  rw [gs_rat_sum]
  rw [S.generatorCount_eq]
  have hsum := S.relator_weightsum_letail c
  have hneg := quadratic_tail_neg c hk
  dsimp [quadraticGSValue] at hneg
  linarith

/-- A negative rational GS evaluation forces the presented group to be infinite. -/
theorem infinite_negative_rat
    {p : ℕ} (FP : FPres.{u} p)
    [Fact p.Prime] [Finite FP.Gen] [Fintype FP.toPresentation.Relator]
    (hsilent : FP.depths.degreeOneSilent)
    {t : ℚ} (ht0 : 0 < t) (ht1 : t < 1)
    (hneg : FP.gsEvalRat t < 0) :
    Infinite FP.Group := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  letI : Finite FP.Group := hfinite
  exact
    (FP.inequalities_rat_bound
      ht0.le ht1 hneg
      (Theorems.rank_sequence_upper FP)
      (Theorems.rank_sequence_pos FP))
      (Theorems.gs_inequalities_fox
        FP hsilent)

/-- An explicit finite shadow relation bound rules out finiteness of its quotient. -/
theorem FSBound.infinite
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : FSBound p d k Q)
    (c : StrictGSParameters d)
    (hkTwo : 2 ≤ k)
    (hk : CuttingTailBound c k) :
    Infinite Q := by
  letI : Fact p.Prime := S.fact_prime
  letI : Finite S.fp.Gen := S.finite_gen
  letI : Fintype S.fp.toPresentation.Relator := S.fintype_relator
  have hinfinite : Infinite S.fp.Group :=
    infinite_negative_rat S.fp
      (fun r => by
        cases hcode : S.relatorCode r with
        | inl j =>
            simpa [hcode] using S.depth_ge r
        | inr i =>
            have hbound := S.depth_ge r
            simp only [hcode] at hbound
            omega)
      c.t0_pos c.t_0_one (S.gs_polyeval_ratneg c hk)
  apply not_finite_iff_infinite.mp
  intro hfinite
  letI : Finite Q := hfinite
  letI : Finite S.fp.Group :=
    Finite.of_equiv Q S.groupEquiv.symm.toEquiv
  exact (not_finite_iff_infinite.mpr hinfinite) inferInstance

/--
The precise Shafarevich relation-bound obligation for one cut quotient:
assuming finiteness produces only the explicitly coded relation data above.
-/
def ShadowRelationBound
    (p d k : ℕ) (Q : Type u) [Group Q] : Prop :=
  Finite Q → Nonempty (FSBound p d k Q)

/--
The direct pro-`p` finite-shadow input for HMR cutting.  Unlike
`FSBound`, this records closed normal generation in a free
pro-`p` group and does not pass through an ordinary free-group presentation.
-/
structure PSRel
    (p d k : ℕ) (Q : Type u) [Group Q] where
  [fact_prime : Fact p.Prime]
  target : Type u
  [targetGroup : Group target]
  [targetTopologicalSpace : TopologicalSpace target]
  free : ProP.FreeGroup.{u} p d
  quotientMap : free.Carrier →* target
  quotientMap_continuous : Continuous quotientMap
  quotientMap_surjective : Function.Surjective quotientMap
  targetEquiv : target ≃* Q
  RelatorIndex : Type u
  [fintype_relator : Fintype RelatorIndex]
  relator : RelatorIndex → free.Carrier
  kernel_eq :
    MonoidHom.ker quotientMap =
      (Subgroup.normalClosure (Set.range relator)).topologicalClosure
  relatorCode : RelatorIndex ↪ (Fin d ⊕ ℕ)
  depth : RelatorIndex → ℕ
  relator_depth :
    ∀ r, relator r ∈
      (zassenhausFiltration p free.Carrier (depth r)).topologicalClosure
  depth_ge : ∀ r,
    match relatorCode r with
    | Sum.inl _ => 2 ≤ depth r
    | Sum.inr i => k + i ≤ depth r

attribute [instance] PSRel.targetGroup
attribute [instance] PSRel.targetTopologicalSpace
attribute [instance] PSRel.fintype_relator

/-- The relators coded as arithmetic Shafarevich relators. -/
noncomputable def PSRel.arithmeticRelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) :
    Finset S.RelatorIndex :=
  by
    classical
    letI : Fintype S.RelatorIndex := S.fintype_relator
    exact Finset.univ.filter fun r =>
      match S.relatorCode r with
      | Sum.inl _ => True
      | Sum.inr _ => False

/-- The relators coded as selected HMR cut relators. -/
noncomputable def PSRel.cutRelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) :
    Finset S.RelatorIndex :=
  by
    classical
    letI : Fintype S.RelatorIndex := S.fintype_relator
    exact Finset.univ.filter fun r =>
      match S.relatorCode r with
      | Sum.inl _ => False
      | Sum.inr _ => True

/-- The index of a selected pro-`p` cut relator. -/
def PSRel.cutIndex
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    (r : S.RelatorIndex) : ℕ :=
  match S.relatorCode r with
  | Sum.inl _ => 0
  | Sum.inr i => i

theorem PSRel.mem_arith_relatorsiff
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) (r : S.RelatorIndex) :
    r ∈ S.arithmeticRelators ↔ ∃ j, S.relatorCode r = Sum.inl j := by
  classical
  letI : Fintype S.RelatorIndex := S.fintype_relator
  cases h : S.relatorCode r with
  | inl j => simp [arithmeticRelators, h]
  | inr i => simp [arithmeticRelators, h]

theorem PSRel.mem_cut_relatorsiff
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) (r : S.RelatorIndex) :
    r ∈ S.cutRelators ↔ ∃ i, S.relatorCode r = Sum.inr i := by
  classical
  letI : Fintype S.RelatorIndex := S.fintype_relator
  cases h : S.relatorCode r with
  | inl j => simp [cutRelators, h]
  | inr i => simp [cutRelators, h]

noncomputable def PSRel.arithmeticIndex
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) (r : S.arithmeticRelators) : Fin d :=
  Classical.choose ((S.mem_arith_relatorsiff r.1).mp r.2)

theorem PSRel.relator_code_arithindex
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) (r : S.arithmeticRelators) :
    S.relatorCode r.1 = Sum.inl (S.arithmeticIndex r) :=
  Classical.choose_spec ((S.mem_arith_relatorsiff r.1).mp r.2)

theorem PSRel.relator_code_cutindex
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) (r : S.RelatorIndex)
    (hr : r ∈ S.cutRelators) :
    S.relatorCode r = Sum.inr (S.cutIndex r) := by
  rcases (S.mem_cut_relatorsiff r).mp hr with ⟨i, hi⟩
  simp [cutIndex, hi]

theorem PSRel.arith_relatordisjoin_cutrelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) :
    Disjoint S.arithmeticRelators S.cutRelators := by
  classical
  rw [Finset.disjoint_left]
  intro r harith hcut
  rcases (S.mem_arith_relatorsiff r).mp harith with ⟨j, hj⟩
  rcases (S.mem_cut_relatorsiff r).mp hcut with ⟨i, hi⟩
  rw [hj] at hi
  cases hi

theorem PSRel.memarith_relatorsor_memcutrelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) (r : S.RelatorIndex) :
    r ∈ S.arithmeticRelators ∨ r ∈ S.cutRelators := by
  classical
  cases h : S.relatorCode r with
  | inl j =>
      exact Or.inl ((S.mem_arith_relatorsiff r).2 ⟨j, h⟩)
  | inr i =>
      exact Or.inr ((S.mem_cut_relatorsiff r).2 ⟨i, h⟩)

theorem PSRel.arith_relators_cardle
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) :
    S.arithmeticRelators.card ≤ d := by
  classical
  let code : S.arithmeticRelators → Fin d := fun r => S.arithmeticIndex r
  have hcode : Function.Injective code := by
    intro r s hrs
    apply Subtype.ext
    apply S.relatorCode.injective
    change S.arithmeticIndex r = S.arithmeticIndex s at hrs
    rw [S.relator_code_arithindex, S.relator_code_arithindex, hrs]
  calc
    S.arithmeticRelators.card = Fintype.card S.arithmeticRelators := by simp
    _ ≤ Fintype.card (Fin d) := Fintype.card_le_of_injective code hcode
    _ = d := Fintype.card_fin d

theorem PSRel.cut_indexinj_cutrelators
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) :
    Set.InjOn S.cutIndex S.cutRelators := by
  intro r hr s hs hrs
  apply S.relatorCode.injective
  rw [S.relator_code_cutindex r hr, S.relator_code_cutindex s hs, hrs]

theorem PSRel.arithmetic_depth_ge
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) (r : S.RelatorIndex)
    (hr : r ∈ S.arithmeticRelators) :
    2 ≤ S.depth r := by
  rcases (S.mem_arith_relatorsiff r).mp hr with ⟨j, hj⟩
  simpa [hj] using S.depth_ge r

theorem PSRel.cut_depth_ge
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q) (r : S.RelatorIndex)
    (hr : r ∈ S.cutRelators) :
    k + S.cutIndex r ≤ S.depth r := by
  simpa [S.relator_code_cutindex r hr] using S.depth_ge r

theorem PSRel.arith_weight_sumle
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ r ∈ S.arithmeticRelators, t ^ S.depth r) ≤ d * t ^ 2 := by
  calc
    (∑ r ∈ S.arithmeticRelators, t ^ S.depth r) ≤
        ∑ _r ∈ S.arithmeticRelators, t ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      apply pow_le_pow_of_le_one ht0 ht1
      exact S.arithmetic_depth_ge r hr
    _ = S.arithmeticRelators.card * t ^ 2 := by simp
    _ ≤ d * t ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast S.arith_relators_cardle) (pow_nonneg ht0 2)

theorem PSRel.cut_weightsum_letail
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    (c : StrictGSParameters d) :
    (∑ r ∈ S.cutRelators, c.t0 ^ S.depth r) ≤
      c.t0 ^ k / (1 - c.t0) := by
  calc
    (∑ r ∈ S.cutRelators, c.t0 ^ S.depth r) ≤
        ∑ r ∈ S.cutRelators, c.t0 ^ (k + S.cutIndex r) := by
      apply Finset.sum_le_sum
      intro r hr
      apply pow_le_pow_of_le_one c.t0_pos.le c.t_0_one.le
      exact S.cut_depth_ge r hr
    _ = ∑ i ∈ S.cutRelators.image S.cutIndex, c.t0 ^ (k + i) := by
      rw [Finset.sum_image S.cut_indexinj_cutrelators]
    _ ≤ c.t0 ^ k / (1 - c.t0) :=
      cut_sum_tail c k (S.cutRelators.image S.cutIndex)

theorem PSRel.relator_weightsum_letail
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    (c : StrictGSParameters d) :
    (∑ r : S.RelatorIndex, c.t0 ^ S.depth r) ≤
      d * c.t0 ^ 2 + c.t0 ^ k / (1 - c.t0) := by
  classical
  letI : Fintype S.RelatorIndex := S.fintype_relator
  have hunion : S.arithmeticRelators ∪ S.cutRelators = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro r
    rcases S.memarith_relatorsor_memcutrelators r with harith | hcut
    · exact Finset.mem_union_left _ harith
    · exact Finset.mem_union_right _ hcut
  rw [← hunion, Finset.sum_union S.arith_relatordisjoin_cutrelators]
  exact add_le_add
    (S.arith_weight_sumle c.t0_pos.le c.t_0_one.le)
    (S.cut_weightsum_letail c)

/-!
## Bounded Vinberg bookkeeping

For the completed pro-`p` route, the natural coefficient sequence consists of
augmentation-layer prefix ranks.  A finite target bounds that sequence but does
not make it finitely supported.  The lemmas below isolate the explicit-depth
weighted-prefix argument needed to turn a negative rational GS value into a
contradiction.
-/

/-- Rationally weighted coefficient mass over the half-open range `[0, N)`. -/
def ratWeightedRange (b : ℕ → ℕ) (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (b n : ℚ) * x ^ n

/-- Rationally weighted coefficient mass shifted by `q`, with terms below the
shift omitted. -/
def ratShiftedRange (b : ℕ → ℕ) (x : ℚ) (N q : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, (if q ≤ n then (b (n - q) : ℚ) else 0) * x ^ n

/-- Adding one degree to a weighted coefficient range adds its final monomial. -/
theorem rat_range_succ (b : ℕ → ℕ) (x : ℚ) (N : ℕ) :
    ratWeightedRange b x (N + 1) =
      ratWeightedRange b x N + (b N : ℚ) * x ^ N := by
  simp [ratWeightedRange, Finset.sum_range_succ]

/-- Weighted coefficient ranges are nonnegative at nonnegative points. -/
theorem rat_range_nonneg
    {b : ℕ → ℕ} {x : ℚ} (hx : 0 ≤ x) (N : ℕ) :
    0 ≤ ratWeightedRange b x N := by
  unfold ratWeightedRange
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (by positivity) (pow_nonneg hx n)

/-- The zeroth coefficient is a lower bound for every nonempty weighted
coefficient range at a nonnegative point. -/
theorem rat_weighted_range
    {b : ℕ → ℕ} {x : ℚ} (hx : 0 ≤ x) (N : ℕ) :
    (b 0 : ℚ) ≤ ratWeightedRange b x (N + 1) := by
  classical
  unfold ratWeightedRange
  have hmem : 0 ∈ Finset.range (N + 1) := by simp
  have hle :
      (b 0 : ℚ) * x ^ 0 ≤
        ∑ k ∈ Finset.range (N + 1), (b k : ℚ) * x ^ k := by
    exact Finset.single_le_sum
      (fun k _hk =>
        mul_nonneg (by exact_mod_cast Nat.zero_le (b k)) (pow_nonneg hx k))
      hmem
  simpa using hle

/-- A shifted weighted coefficient range is a monomial times an initial
weighted coefficient range. -/
theorem rat_shifted_range
    (b : ℕ → ℕ) (x : ℚ) {N q : ℕ} (hq : q ≤ N) :
    ratShiftedRange b x N q =
      x ^ q * ratWeightedRange b x (N - q) := by
  unfold ratShiftedRange ratWeightedRange
  rw [show N = q + (N - q) by omega, Finset.sum_range_add]
  have hzero :
      (∑ n ∈ Finset.range q,
        (if q ≤ n then (b (n - q) : ℚ) else 0) * x ^ n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnq : ¬ q ≤ n := by
      have hnlt := Finset.mem_range.mp hn
      omega
    simp [hnq]
  rw [hzero, zero_add, Nat.add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [if_pos (Nat.le_add_right q n), Nat.add_sub_cancel_left]
  rw [pow_add]
  ring

/-- Weighted coefficient ranges are monotone in their upper endpoint at a
nonnegative point. -/
theorem rat_weighted_mono
    {b : ℕ → ℕ} {x : ℚ} (hx : 0 ≤ x) {M N : ℕ} (hMN : M ≤ N) :
    ratWeightedRange b x M ≤ ratWeightedRange b x N := by
  unfold ratWeightedRange
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp at hn ⊢
    omega
  · intro n hnN hnM
    exact mul_nonneg (by positivity) (pow_nonneg hx n)

/-- A shifted range is bounded by its monomial times the full coefficient
range. -/
theorem rat_weighted_shifted
    {b : ℕ → ℕ} {x : ℚ} (hx : 0 ≤ x) (N q : ℕ) :
    ratShiftedRange b x N q ≤
      x ^ q * ratWeightedRange b x N := by
  by_cases hq : q ≤ N
  · rw [rat_shifted_range b x hq]
    apply mul_le_mul_of_nonneg_left
    · exact rat_weighted_mono hx (Nat.sub_le N q)
    · exact pow_nonneg hx q
  · have hzero : ratShiftedRange b x N q = 0 := by
      unfold ratShiftedRange
      apply Finset.sum_eq_zero
      intro n hn
      have hnq : ¬ q ≤ n := by
        have hnlt := Finset.mem_range.mp hn
        omega
      simp [hnq]
    rw [hzero]
    exact mul_nonneg (pow_nonneg hx q) (rat_range_nonneg hx N)

/-- The weighted generator shift through degree `N` is `x` times the weighted
coefficient range through degree `N - 1`. -/
theorem rat_full_range
    (b : ℕ → ℕ) (x : ℚ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      (if 1 ≤ n then (b (n - 1) : ℚ) else 0) * x ^ n) =
        x * ratWeightedRange b x N := by
  rw [Finset.sum_range_succ']
  simp [ratWeightedRange, Finset.mul_sum, pow_succ, mul_comm, mul_assoc]

/-- Rationally weighted mass of the full explicit-depth Vinberg balances. -/
def ratBalanceRange {r : ℕ}
    (d : ℕ) (b : ℕ → ℕ) (depth : Fin r → ℕ) (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N,
    ((b n : ℚ) +
        (∑ i, if depth i ≤ n then (b (n - depth i) : ℚ) else 0) -
      (d : ℚ) * (if 1 ≤ n then (b (n - 1) : ℚ) else 0)) * x ^ n

/-- Full Vinberg inequalities make every weighted balance range nonnegative at
a nonnegative point. -/
theorem rat_balance_nonneg
    {d r : ℕ} {b : ℕ → ℕ} {depth : Fin r → ℕ} {x : ℚ}
    (hx : 0 ≤ x)
    (hineq : ∀ n, GShafar.fullCoefficientInequality d b depth n)
    (N : ℕ) :
    0 ≤ ratBalanceRange d b depth x N := by
  unfold ratBalanceRange
  apply Finset.sum_nonneg
  intro n hn
  apply mul_nonneg
  · have h := hineq n
    unfold GShafar.fullCoefficientInequality
      GShafar.fullNatTerm
      GShafar.fullRelatorTerm at h
    have hq :
        (d : ℚ) * (if 1 ≤ n then (b (n - 1) : ℚ) else 0) ≤
          (b n : ℚ) + ∑ i, if depth i ≤ n then (b (n - depth i) : ℚ) else 0 := by
      exact_mod_cast h
    exact sub_nonneg.mpr hq
  · exact pow_nonneg hx n

/-- The weighted relator convolution is bounded by the relator-weight sum times
the full weighted coefficient range. -/
theorem rat_weighted_full
    {r : ℕ} {b : ℕ → ℕ} {depth : Fin r → ℕ} {x : ℚ}
    (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (∑ i, if depth i ≤ n then (b (n - depth i) : ℚ) else 0) * x ^ n) ≤
        (∑ i, x ^ depth i) * ratWeightedRange b x N := by
  calc
    (∑ n ∈ Finset.range N,
        (∑ i, if depth i ≤ n then (b (n - depth i) : ℚ) else 0) * x ^ n) =
        ∑ i, ratShiftedRange b x N (depth i) := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          rfl
    _ ≤ ∑ i, x ^ depth i * ratWeightedRange b x N := by
      apply Finset.sum_le_sum
      intro i hi
      exact rat_weighted_shifted hx N (depth i)
    _ = (∑ i, x ^ depth i) * ratWeightedRange b x N := by
      rw [Finset.sum_mul]

/-- A finite weighted balance range is bounded by the GS value times the
coefficient range and the single generator boundary term. -/
theorem rat_balance_range
    {d r : ℕ} {b : ℕ → ℕ} {depth : Fin r → ℕ} {x : ℚ}
    (hx : 0 ≤ x) (N : ℕ) :
    ratBalanceRange d b depth x (N + 1) ≤
      (1 - (d : ℚ) * x + ∑ i, x ^ depth i) *
          ratWeightedRange b x (N + 1) +
        (d : ℚ) * (b N : ℚ) * x ^ (N + 1) := by
  rw [ratBalanceRange]
  have hrel := rat_weighted_full (b := b) (depth := depth) hx (N + 1)
  calc
    (∑ n ∈ Finset.range (N + 1),
      ((b n : ℚ) +
          (∑ i, if depth i ≤ n then (b (n - depth i) : ℚ) else 0) -
        (d : ℚ) * (if 1 ≤ n then (b (n - 1) : ℚ) else 0)) * x ^ n) =
      ratWeightedRange b x (N + 1) +
          (∑ n ∈ Finset.range (N + 1),
            (∑ i, if depth i ≤ n then (b (n - depth i) : ℚ) else 0) * x ^ n) -
        (d : ℚ) * (x * ratWeightedRange b x N) := by
          simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
            mul_assoc, ← Finset.mul_sum]
          rw [rat_full_range]
          rfl
    _ ≤ ratWeightedRange b x (N + 1) +
          (∑ i, x ^ depth i) * ratWeightedRange b x (N + 1) -
        (d : ℚ) * (x * ratWeightedRange b x N) := by
          linarith
    _ = (1 - (d : ℚ) * x + ∑ i, x ^ depth i) *
          ratWeightedRange b x (N + 1) +
        (d : ℚ) * (b N : ℚ) * x ^ (N + 1) := by
          rw [rat_range_succ b x N, pow_succ]
          ring

/-- A bounded positive sequence cannot satisfy the explicit-depth Vinberg
recurrence when the corresponding GS expression is negative in `[0, 1)`. -/
theorem full_inequalities_neg
    {d r : ℕ} {b : ℕ → ℕ} {B : ℕ} {depth : Fin r → ℕ} {x : ℚ}
    (hx : 0 ≤ x) (hx1 : x < 1)
    (hneg : 1 - (d : ℚ) * x + ∑ i, x ^ depth i < 0)
    (hbound : ∀ n, b n ≤ B)
    (hb0 : 0 < b 0)
    (hineq : ∀ n, GShafar.fullCoefficientInequality d b depth n) :
    False := by
  let E : ℚ := 1 - (d : ℚ) * x + ∑ i, x ^ depth i
  let C : ℚ := (d : ℚ) * (B : ℚ)
  have hE : E < 0 := by simpa [E] using hneg
  have hb0q : (0 : ℚ) < b 0 := by exact_mod_cast hb0
  have hε : 0 < -(E * (b 0 : ℚ)) := by
    exact neg_pos.mpr (mul_neg_of_neg_of_pos hE hb0q)
  have hC : 0 ≤ C := by positivity
  have hC1 : 0 < C + 1 := by linarith
  obtain ⟨N, hpow⟩ :=
    exists_pow_lt_of_lt_one (div_pos hε hC1) hx1
  have hx_le_one : x ≤ 1 := le_of_lt hx1
  have hpow_succ : x ^ (N + 1) ≤ x ^ N := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hx N) hx_le_one
  have hboundary :
      (d : ℚ) * (b N : ℚ) * x ^ (N + 1) < -(E * (b 0 : ℚ)) := by
    calc
      (d : ℚ) * (b N : ℚ) * x ^ (N + 1) ≤ C * x ^ (N + 1) := by
        dsimp [C]
        gcongr
        exact_mod_cast hbound N
      _ ≤ (C + 1) * x ^ N := by
        calc
          C * x ^ (N + 1) ≤ C * x ^ N :=
            mul_le_mul_of_nonneg_left hpow_succ hC
          _ ≤ (C + 1) * x ^ N := by
            apply mul_le_mul_of_nonneg_right
            · linarith
            · exact pow_nonneg hx N
      _ < -(E * (b 0 : ℚ)) := by
        simpa [mul_comm] using (lt_div_iff₀ hC1).mp hpow
  have hprefix :
      (b 0 : ℚ) ≤ ratWeightedRange b x (N + 1) :=
    rat_weighted_range hx N
  have hmain :
      E * ratWeightedRange b x (N + 1) ≤ E * (b 0 : ℚ) :=
    mul_le_mul_of_nonpos_left hprefix (le_of_lt hE)
  have hnonneg :=
    rat_balance_nonneg hx hineq (N + 1)
  have hupper :=
    rat_balance_range (d := d) (b := b) (depth := depth) hx N
  change
    ratBalanceRange d b depth x (N + 1) ≤
      E * ratWeightedRange b x (N + 1) +
        (d : ℚ) * (b N : ℚ) * x ^ (N + 1) at hupper
  linarith

/--
The augmentation-layer prefix-rank data for a finite quotient of a free
pro-`p` group by closed normally generating relators.

This is the direct pro-`p` Fox/Hilbert input.  The coefficient sequence is the
augmentation-layer prefix-rank sequence of the finite target group algebra.
Its uniform bound is the dimension of that algebra; the displayed inequality
is the filtered Vinberg relation-module estimate.
-/
theorem PSRel.existsaug_layerprefix_rankdatafin
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    [Finite S.target] :
    ∃ (B : ℕ) (a : ℕ → ℕ),
      FPres.SUBound a B ∧
        0 < a 0 ∧
          ∀ n,
            d * (if 1 ≤ n then a (n - 1) else 0) ≤
              a n +
                ∑ r : S.RelatorIndex,
                  if S.depth r ≤ n then a (n - S.depth r) else 0 := by
  classical
  letI : Fact p.Prime := S.fact_prime
  refine
    ⟨Nat.card S.target,
      ProP.completedPrefixRank p S.target, ?_, ?_, ?_⟩
  · exact
      ProP.completed_rank_upper
        p S.target
  · exact
      ProP.completed_rank_pos p S.target
  · intro n
    exact
      ProP.completed_fox_inequality
        S.free S.quotientMap S.quotientMap_continuous S.quotientMap_surjective
        S.relator S.kernel_eq S.depth S.relator_depth n

theorem PSRel.sum_powdepth_fineq
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    {R : Type*} [CommSemiring R] (t : R) :
    (∑ i : Fin (Fintype.card S.RelatorIndex),
        t ^ S.depth ((Fintype.equivFin S.RelatorIndex).symm i)) =
      ∑ r : S.RelatorIndex, t ^ S.depth r := by
  classical
  exact
    Fintype.sum_equiv (Fintype.equivFin S.RelatorIndex).symm _ _
      (fun _ => rfl)

/-- A finite completed pro-`p` shadow cannot have a negative GS value at a
point in `[0, 1)`. -/
theorem PSRel.falsefin_gsexpression_ratneg
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    [Finite S.target]
    {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hneg : 1 - (d : ℚ) * t + ∑ r : S.RelatorIndex, t ^ S.depth r < 0) :
    False := by
  classical
  rcases S.existsaug_layerprefix_rankdatafin with
    ⟨B, b, hbound, hb0, hfull⟩
  let depthFin : Fin (Fintype.card S.RelatorIndex) → ℕ :=
    fun i => S.depth ((Fintype.equivFin S.RelatorIndex).symm i)
  have hfullFin :
      ∀ n, GShafar.fullCoefficientInequality d b depthFin n := by
    intro n
    unfold GShafar.fullCoefficientInequality
      GShafar.fullNatTerm
      GShafar.fullRelatorTerm
    rw [show
      (∑ i : Fin (Fintype.card S.RelatorIndex),
          if depthFin i ≤ n then b (n - depthFin i) else 0) =
        ∑ r : S.RelatorIndex,
          if S.depth r ≤ n then b (n - S.depth r) else 0 by
      exact
        Fintype.sum_equiv (Fintype.equivFin S.RelatorIndex).symm _ _
          (fun _ => rfl)]
    exact hfull n
  have hnegFin :
      1 - (d : ℚ) * t + ∑ i, t ^ depthFin i < 0 := by
    rw [S.sum_powdepth_fineq]
    exact hneg
  exact
    full_inequalities_neg
      ht0 ht1 hnegFin hbound hb0 hfullFin

theorem PSRel.gs_expression_ratneg
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    (c : StrictGSParameters d)
    (hk : CuttingTailBound c k) :
    1 - (d : ℚ) * c.t0 + ∑ r : S.RelatorIndex, c.t0 ^ S.depth r < 0 := by
  have hsum := S.relator_weightsum_letail c
  have hneg := quadratic_tail_neg c hk
  dsimp [quadraticGSValue] at hneg
  linarith

/--
Bounded-prefix Vinberg contradiction for a free pro-`p` quotient with closed
normally generating relators.  This is the direct pro-`p` GS theorem needed by
HMR cutting; proving it must not introduce an ordinary free-group normal-closure
comparison.
-/
theorem PSRel.infinite
    {p d k : ℕ} {Q : Type u} [Group Q]
    (S : PSRel p d k Q)
    (c : StrictGSParameters d)
    (_hkTwo : 2 ≤ k)
    (hk : CuttingTailBound c k) :
    Infinite Q := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  letI : Finite Q := hfinite
  letI : Finite S.target :=
    Finite.of_equiv Q S.targetEquiv.symm.toEquiv
  have hneg := S.gs_expression_ratneg c hk
  exact
    S.falsefin_gsexpression_ratneg c.t0_pos.le c.t_0_one hneg

/--
The truthful pro-`p` Shafarevich relation-bound obligation for one cut
quotient: finiteness produces closed normally generating relators with the
explicit HMR depth coding.
-/
def ProShadowBound
    (p d k : ℕ) (Q : Type u) [Group Q] : Prop :=
  Finite Q → Nonempty (PSRel p d k Q)

/-- A family of HMR cut quotients. -/
structure CSystem (p : ℕ) (G : Type u) [Group G] where
  quotient : (ℕ → G) → Type u
  [quotientGroup : ∀ x, Group (quotient x)]
  admissible : ℕ → (ℕ → G) → Prop

attribute [instance] CSystem.quotientGroup

/--
Application-specific finite-shadow adapter: every finite admissible cut
quotient has the explicit relation coding above.

This packages presentation construction and cut-relator bookkeeping. It is
intentionally distinct from the arithmetic Shafarevich inequality `r ≤ d`.
-/
def CSystem.FinShadowRelbounds
    {p : ℕ} {G : Type u} [Group G]
    (S : CSystem p G) (d : ℕ) : Prop :=
  ∀ ⦃k : ℕ⦄, ∀ x : ℕ → G,
    S.admissible k x →
      ShadowRelationBound p d k (S.quotient x)

/--
Application-specific direct pro-`p` finite-shadow adapter: every finite
admissible cut quotient has the closed-normal-generation relation coding
above.
-/
def CSystem.PropFinshadowRelbounds
    {p : ℕ} {G : Type u} [Group G]
    (S : CSystem p G) (d : ℕ) : Prop :=
  ∀ ⦃k : ℕ⦄, ∀ x : ℕ → G,
    S.admissible k x →
      ProShadowBound p d k (S.quotient x)

/--
Reusable HMR cutting theorem. Its input is the explicit finite-shadow
presentation adapter; the GS contradiction is proved above.
-/
theorem CSystem.infinite_quot_tailbound
    {p : ℕ} {G : Type u} [Group G]
    (S : CSystem p G) {d : ℕ} (c : StrictGSParameters d)
    (hshadow : S.FinShadowRelbounds d)
    {k : ℕ} (hkTwo : 2 ≤ k) (hk : CuttingTailBound c k)
    (x : ℕ → G) (hx : S.admissible k x) :
    Infinite (S.quotient x) := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  letI : Finite (S.quotient x) := hfinite
  rcases hshadow x hx inferInstance with ⟨R⟩
  exact (not_finite_iff_infinite.mpr (R.infinite c hkTwo hk)) inferInstance

/--
Reusable direct pro-`p` HMR cutting theorem.  The application supplies
closed-normal-generation data, and the pro-`p` GS recurrence gives the
infinitude contradiction.
-/
theorem CSystem.infinitequot_prop_tailbound
    {p : ℕ} {G : Type u} [Group G]
    (S : CSystem p G) {d : ℕ} (c : StrictGSParameters d)
    (hshadow : S.PropFinshadowRelbounds d)
    {k : ℕ} (hkTwo : 2 ≤ k) (hk : CuttingTailBound c k)
    (x : ℕ → G) (hx : S.admissible k x) :
    Infinite (S.quotient x) := by
  apply not_finite_iff_infinite.mp
  intro hfinite
  letI : Finite (S.quotient x) := hfinite
  rcases hshadow x hx inferInstance with ⟨R⟩
  exact (not_finite_iff_infinite.mpr (R.infinite c hkTwo hk)) inferInstance

end HPGs
end Towers
