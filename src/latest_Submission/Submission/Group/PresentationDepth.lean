import Submission.Group.Words
import Submission.Group.Frattini
import Submission.Group.Zassenhaus
import Mathlib.Algebra.TrivSqZeroExt.Basic

open scoped commutatorElement

namespace Submission

open scoped IsMulCommutative
namespace Group

universe u v w
open Submission.Topology

/-- Filtered quotient-presentation data: a presentation, a filtration on its
presented group, and depth labels compatible with the quotient map. -/
structure fPTheory where
  Gen : Type u
  pres : presentations.{u}
  gen_equiv : Gen ≃ pres.Gen
  filtration : DFilt pres.Group
  /-- Filtration on the free group where relator depths are actually measured. -/
  freeFiltration : DFilt pres.Free
  relDepth : pres.rels → ℕ
  relators_killed : ∀ r : pres.rels, pres.quotientMap r.1 = 1
  relDepth_sound : ∀ r : pres.rels, pres.quotientMap r.1 ∈ filtration (relDepth r)
  /-- Relator depths are exact in the free-group filtration, not merely after quotienting. -/
  rel_free_exact : ∀ r : pres.rels, exactDepth freeFiltration r.1 (relDepth r)
  depth_positive : ∀ r : pres.rels, 0 < relDepth r
  quotient_surjective : Function.Surjective pres.quotientMap

/-- Relators are killed by the quotient map. -/
theorem fPTheory.relator_killed
    (T : fPTheory) (r : T.pres.rels) :
    T.pres.quotientMap r.1 = 1 :=
  T.relators_killed r

/-- Relators lie in their recorded filtration depths after quotient evaluation. -/
theorem fPTheory.relDepth_mem
    (T : fPTheory) (r : T.pres.rels) :
    T.pres.quotientMap r.1 ∈ T.filtration (T.relDepth r) :=
  T.relDepth_sound r

/-- Relators have the recorded exact depth in the free-group filtration. -/
theorem fPTheory.rel_depth_exactfree
    (T : fPTheory) (r : T.pres.rels) :
    exactDepth T.freeFiltration r.1 (T.relDepth r) :=
  T.rel_free_exact r

/-- Recorded relator depths are positive. -/
theorem fPTheory.relDepth_pos
    (T : fPTheory) (r : T.pres.rels) :
    0 < T.relDepth r :=
  T.depth_positive r

/-- The presentation quotient map is surjective. -/
theorem fPTheory.quotient_surj
    (T : fPTheory) : Function.Surjective T.pres.quotientMap :=
  T.quotient_surjective


/-- A package of lower-bound and exact-depth assertions for one element. -/
structure dStatem {G : Type u} [Group G] (F : DFilt G) (x : G) where
  lower : Set ℕ
  exact : Option ℕ
  lower_sound : ∀ n, n ∈ lower → x ∈ F n
  lower_complete : ∀ n, x ∈ F n → n ∈ lower
  lower_downward : ∀ {m n}, n ∈ lower → m ≤ n → m ∈ lower
  exact_sound : ∀ n, exact = some n → exactDepth F x n
  exact_complete : ∀ n, exactDepth F x n → exact = some n

/-- Soundness of a recorded exact depth. -/
theorem dStatem.exact_depth_eq {G : Type u} [Group G]
    {F : DFilt G} {x : G} (D : dStatem F x)
    {n : ℕ} (h : D.exact = some n) : exactDepth F x n :=
  D.exact_sound n h

/-- The recorded lower-bound set is complete for actual membership. -/
theorem dStatem.lower_iff {G : Type u} [Group G]
    {F : DFilt G} {x : G} (D : dStatem F x) (n : ℕ) :
    n ∈ D.lower ↔ x ∈ F n :=
  ⟨D.lower_sound n, D.lower_complete n⟩

/-- Any actual exact depth is the recorded exact depth. -/
theorem dStatem.exact_eq_depth {G : Type u} [Group G]
    {F : DFilt G} {x : G} (D : dStatem F x)
    {n : ℕ} (hn : exactDepth F x n) : D.exact = some n :=
  D.exact_complete n hn

/-- Soundness of a recorded lower bound. -/
theorem dStatem.mem_of_lower {G : Type u} [Group G]
    {F : DFilt G} {x : G} (D : dStatem F x)
    {n : ℕ} (hn : n ∈ D.lower) : x ∈ F n :=
  D.lower_sound n hn

/-- Exact-depth uniqueness is inherited from `Option`, not stored as independent data. -/
theorem dStatem.exact_unique {G : Type u} [Group G]
    {F : DFilt G} {x : G} (D : dStatem F x)
    {m n : ℕ} (hm : D.exact = some m) (hn : D.exact = some n) : m = n := by
  rw [hm] at hn
  exact Option.some.inj hn


/-- Active relators in a specified degree window. -/
def activeRelators {α : Type u} (R : relatorSet α) (d : R → ℕ) (n : ℕ) : Set R :=
  {r | d r ≤ n}

/-- Refined depth bookkeeping for a relator set. -/
structure rDBookke {α : Type u} (R : relatorSet α) where
  lower : R → ℕ
  exact? : R → Option ℕ
  exact_ge_lower : ∀ r n, exact? r = some n → lower r ≤ n
  activeAt : ℕ → Set R := fun n => {r | lower r ≤ n}
  active_spec : ∀ n r, r ∈ activeAt n ↔ lower r ≤ n
  active_mono : ∀ {m n}, m ≤ n → activeAt m ⊆ activeAt n
  exact_sound_lower : ∀ r n, exact? r = some n → r ∈ activeAt n



/-- Unfolded membership criterion for refined active relators. -/
theorem rDBookke.mem_active_iff {α : Type u} {R : relatorSet α}
    (B : rDBookke R) (n : ℕ) (r : R) :
    r ∈ B.activeAt n ↔ B.lower r ≤ n := B.active_spec n r

/-- Exact depth witnesses are active at that exact degree. -/
theorem rDBookke.active_of_exact {α : Type u} {R : relatorSet α}
    (B : rDBookke R) {r : R} {n : ℕ} (h : B.exact? r = some n) :
    r ∈ B.activeAt n := B.exact_sound_lower r n h

/-- Refined active sets are monotone, pointwise form. -/
theorem rDBookke.active_mono_apply {α : Type u} {R : relatorSet α}
    (B : rDBookke R) {m n : ℕ} (h : m ≤ n) {r : R}
    (hr : r ∈ B.activeAt m) : r ∈ B.activeAt n :=
  B.active_mono h hr

/-- Ingredients/laws for a `p`-central series.  The fields record the two
closure estimates used by Zassenhaus-style arguments. -/
structure pSIngred (p : ℕ) (G : Type u) [Group G] where
  prime : Nat.Prime p
  series : ℕ → Subgroup G
  top : series 0 = ⊤
  antitone : Antitone series
  normal : ∀ n, (series n).Normal
  commutator_mem : ∀ m n (x y : G), x ∈ series m → y ∈ series n →
    x * y * x⁻¹ * y⁻¹ ∈ series (m + n)
  ppower_mem : ∀ n (x : G), x ∈ series n → x ^ p ∈ series (p * n)

/-- The displayed exponent for a p-central series is prime. -/
theorem pSIngred.prime_p {p : ℕ} {G : Type u} [Group G]
    (S : pSIngred p G) : Nat.Prime p :=
  S.prime

/-- A p-central series package supplies the usual prime fact for its exponent. -/
@[reducible] def pSIngred.fact_prime {p : ℕ} {G : Type u} [Group G]
    (S : pSIngred p G) : Fact p.Prime :=
  ⟨S.prime⟩

/-- The p-central series starts at the top subgroup. -/
theorem pSIngred.series_zero {p : ℕ} {G : Type u} [Group G]
    (S : pSIngred p G) : S.series 0 = ⊤ :=
  S.top

/-- Named antitonicity accessor for a p-central series. -/
theorem pSIngred.mono {p : ℕ} {G : Type u} [Group G]
    (S : pSIngred p G) {m n : ℕ} (h : m ≤ n) :
    S.series n ≤ S.series m :=
  S.antitone h

/-- Each term of a p-central series is normal. -/
theorem pSIngred.normal_term {p : ℕ} {G : Type u} [Group G]
    (S : pSIngred p G) (n : ℕ) : (S.series n).Normal :=
  S.normal n

/-- Two-index commutator closure for a p-central series. -/
theorem pSIngred.commutator_mem' {p : ℕ} {G : Type u} [Group G]
    (S : pSIngred p G) {m n : ℕ} {x y : G}
    (hx : x ∈ S.series m) (hy : y ∈ S.series n) :
    x * y * x⁻¹ * y⁻¹ ∈ S.series (m + n) :=
  S.commutator_mem m n x y hx hy

/-- Named p-power closure accessor. -/
theorem pSIngred.pow_mem {p : ℕ} {G : Type u} [Group G]
    (S : pSIngred p G) {n : ℕ} {x : G} (hx : x ∈ S.series n) :
    x ^ p ∈ S.series (p * n) :=
  S.ppower_mem n x hx


/-- An initial form in an associated graded object. -/
structure fAGraded (A : ℕ → Type u) where
  [zeroA : ∀ n, Zero (A n)]
  degree : ℕ
  value : A degree
  nonzero : value ≠ 0
  representative : Type u
  representative_degree : representative → ℕ
  representative_value : representative → A degree
  representative_has_degree : ∀ r, representative_degree r = degree
  realizes_value : ∃ r, representative_value r = value

/-- The initial form value is nonzero. -/
theorem fAGraded.value_ne_zero {A : ℕ → Type u}
    (I : fAGraded A) :
    (letI := I.zeroA I.degree; I.value ≠ 0) := by
  exact I.nonzero

/-- Some representative realizes the displayed initial value. -/
theorem fAGraded.exists_representative_value {A : ℕ → Type u}
    (I : fAGraded A) : ∃ r, I.representative_value r = I.value :=
  I.realizes_value

/-- Representatives all have the recorded degree. -/
theorem fAGraded.rep_degree {A : ℕ → Type u}
    (I : fAGraded A) (r : I.representative) :
    I.representative_degree r = I.degree :=
  I.representative_has_degree r


/-- A graded dimension sequence. -/
abbrev gradedDimensionSequence (_R : Type u) := ℕ → Cardinal

/-- A Hilbert series represented by its coefficient sequence. -/
abbrev hilbertSeries (R : Type u) := ℕ → R

/-- The `n`th Hilbert coefficient. -/
def hilbertCoefficientA {R : Type u} (H : hilbertSeries R) (n : ℕ) : R := H n

/-- Relator-count coefficient in degree `n`. -/
noncomputable def relatorCountR {α : Type u} {R : relatorSet α}
    (d : R → ℕ) (n : ℕ) : ℕ :=
  Nat.card {r : R // d r = n}

/-- A weighted degree function on atoms. -/
abbrev weightedDegree (α : Type u) := α → ℕ

/-- The subgroup generated by commutators. -/
def commutatorSubgroup (G : Type u) [Group G] : Subgroup G :=
  Subgroup.closure (commutators G)

/-- The subgroup generated by `p`-powers. -/
def pPowerSubgroup (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  Subgroup.closure (pPowers p G)

/-- The mod-`p` abelianization normal subgroup, generated by `p`-powers and commutators. -/
def mAKern (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  Subgroup.normalClosure (pPowers p G ∪ commutators G)

instance mAKern.normal (p : ℕ) (G : Type u) [Group G] :
    (mAKern p G).Normal :=
  Subgroup.normalClosure_normal

/-- The mod-`p` abelianization quotient. -/
def modPAbelianization (p : ℕ) (G : Type u) [Group G] : Type u :=
  G ⧸ mAKern p G

/-- The Frattini subgroup model used for `p`-groups: generated by `G^p` and commutators. -/
def fSubgro (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  mAKern p G

/-- The same Frattini subgroup model, with the finite `p`-group hypothesis made explicit. -/
def frattiniSubgroupGroup (p : ℕ) (G : Type u) [Group G]
    (_hG : fPGroups p G) : Subgroup G :=
  fSubgro p G

instance fSubgro.normal (p : ℕ) (G : Type u) [Group G] :
    (fSubgro p G).Normal := by
  dsimp [fSubgro]
  infer_instance

/-- Every `p`th power lies in the Frattini subgroup model. -/
theorem ppower_mem_frattini (p : ℕ) {G : Type u} [Group G] (g : G) :
    g ^ p ∈ fSubgro p G := by
  dsimp [fSubgro, mAKern]
  apply Subgroup.subset_normalClosure
  exact Or.inl ⟨g, rfl⟩

/-- Every group commutator lies in the Frattini subgroup model. -/
theorem commutator_mem_frattini (p : ℕ) {G : Type u} [Group G] (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ fSubgro p G := by
  dsimp [fSubgro, mAKern]
  apply Subgroup.subset_normalClosure
  exact Or.inr ⟨(x, y), rfl⟩

/-- The finite `p`-group wrapper is definitionally the Frattini subgroup model. -/
@[simp] theorem frattini_subgroup_group (p : ℕ) (G : Type u) [Group G]
    (hG : fPGroups p G) :
    frattiniSubgroupGroup p G hG = fSubgro p G := rfl


/-- The Frattini subgroup as a packaged normal subgroup. -/
def frattiniNormalSubgroup (p : ℕ) (G : Type u) [Group G] : nSubgro G where
  carrier := fSubgro p G
  normal' := fSubgro.normal p G

/-- The Frattini quotient. -/
abbrev frattiniQuotient (p : ℕ) (G : Type u) [Group G] : Type u :=
  quotientGroup (frattiniNormalSubgroup p G)

/-- The Frattini quotient with the finite `p`-group hypothesis made explicit. -/
abbrev frattiniPGroup (p : ℕ) (G : Type u) [Group G]
    (_hG : fPGroups p G) : Type u :=
  frattiniQuotient p G

/-- Canonical projection to the Frattini quotient. -/
def frattiniProjection (p : ℕ) (G : Type u) [Group G] : G →* frattiniQuotient p G :=
  (frattiniNormalSubgroup p G).projection

/-- The Frattini projection is surjective. -/
theorem frattiniProjection_surjective (p : ℕ) (G : Type u) [Group G] :
    Function.Surjective (frattiniProjection p G) :=
  (frattiniNormalSubgroup p G).projection_surjective

/-- Its kernel is the Frattini subgroup. -/
theorem frattiniProjection_kernel (p : ℕ) (G : Type u) [Group G] :
    MonoidHom.ker (frattiniProjection p G) = fSubgro p G :=
  (frattiniNormalSubgroup p G).ker_projection

/-- The Frattini projection kills `p`th powers. -/
@[simp] theorem frattiniProjection_pow (p : ℕ) {G : Type u} [Group G] (g : G) :
    frattiniProjection p G (g ^ p) = 1 := by
  have hmem : g ^ p ∈ MonoidHom.ker (frattiniProjection p G) := by
    rw [frattiniProjection_kernel]
    exact ppower_mem_frattini p g
  exact hmem

/-- The Frattini projection kills commutators. -/
@[simp] theorem frattiniProjection_commutator (p : ℕ) {G : Type u} [Group G]
    (x y : G) : frattiniProjection p G (x * y * x⁻¹ * y⁻¹) = 1 := by
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ MonoidHom.ker (frattiniProjection p G) := by
    rw [frattiniProjection_kernel]
    exact commutator_mem_frattini p x y
  exact hmem


/-- Degree-one generator rank: the least cardinality of a generating subset of
the Frattini quotient.  For finite `p`-groups this agrees (by Burnside basis) with
the `𝔽_p`-dimension of `G/Φ(G)`, unlike the raw cardinality of the quotient. -/
noncomputable def degreeGeneratorRank (p : ℕ) (G : Type u) [Group G] : Cardinal :=
  sInf {c : Cardinal | ∃ S : Set (frattiniQuotient p G),
    Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c}

/-- Generator number `d` for a chosen generating set. -/
noncomputable def generatorNumberD {G : Type u} [Group G] (S : Set G) : Cardinal :=
  Cardinal.mk S

/-- Data used by degree-one Burnside machinery, including the canonical
Frattini projection and a chosen minimal generating family in degree one. -/
structure dBMachin (p : ℕ) (G : Type u) [Group G] where
  prime : Nat.Prime p
  quotient : Type u := frattiniQuotient p G
  quotientEquiv : quotient ≃ frattiniQuotient p G
  rank : Cardinal := degreeGeneratorRank p G
  projection : G →* frattiniQuotient p G := QuotientGroup.mk' (fSubgro p G)
  projection_surjective : Function.Surjective projection
  projection_ppower : ∀ g : G, projection (g ^ p) = 1
  projection_commutator : ∀ x y : G, projection (x * y * x⁻¹ * y⁻¹) = 1
  generators : Set G
  minimal_generators : minimalGeneratingSet G generators

/-- Constructor for degree-one Burnside data using the canonical Frattini projection. -/
noncomputable def dBMachin.ofGenerators (p : ℕ) (G : Type u) [Group G]
    (hp : Nat.Prime p) (S : Set G) (hmin : minimalGeneratingSet G S)
    (hppow : ∀ g : G, frattiniProjection p G (g ^ p) = 1)
    (hcomm : ∀ x y : G, frattiniProjection p G (x * y * x⁻¹ * y⁻¹) = 1) :
    dBMachin p G where
  prime := hp
  quotientEquiv := Equiv.refl _
  projection := frattiniProjection p G
  projection_surjective := frattiniProjection_surjective p G
  projection_ppower := hppow
  projection_commutator := hcomm
  generators := S
  minimal_generators := hmin

/-- Canonical degree-one Burnside data from a minimal generating set. -/
noncomputable def dBMachin.ofMinimalGenerators (p : ℕ)
    (G : Type u) [Group G] (hp : Nat.Prime p) (S : Set G) (hmin : minimalGeneratingSet G S) :
    dBMachin p G :=
  dBMachin.ofGenerators p G hp S hmin
    (fun g => frattiniProjection_pow p g)
    (fun x y => frattiniProjection_commutator p x y)

/-- The recorded quotient is identified with the canonical Frattini quotient. -/
def dBMachin.quotient_equiv {p : ℕ} {G : Type u} [Group G]
    (B : dBMachin p G) : B.quotient ≃ frattiniQuotient p G :=
  B.quotientEquiv

/-- The exponent in degree-one Burnside machinery is prime. -/
theorem dBMachin.prime_p {p : ℕ} {G : Type u} [Group G]
    (B : dBMachin p G) : Nat.Prime p := B.prime

/-- Degree-one Burnside data supplies the usual prime fact for its exponent. -/
@[reducible] def dBMachin.fact_prime {p : ℕ} {G : Type u} [Group G]
    (B : dBMachin p G) : Fact p.Prime :=
  ⟨B.prime⟩

/-- Named projection: the Burnside degree-one map is surjective. -/
theorem dBMachin.projection_surj {p : ℕ} {G : Type u} [Group G]
    (B : dBMachin p G) : Function.Surjective B.projection :=
  B.projection_surjective

/-- Named projection: the Burnside degree-one map kills `p`th powers. -/
@[simp] theorem dBMachin.projection_pow_eqone {p : ℕ}
    {G : Type u} [Group G] (B : dBMachin p G) (g : G) :
    B.projection (g ^ p) = 1 :=
  B.projection_ppower g

/-- Named projection: the Burnside degree-one map kills commutators. -/
@[simp] theorem dBMachin.projection_comm_eqone {p : ℕ}
    {G : Type u} [Group G] (B : dBMachin p G) (x y : G) :
    B.projection (x * y * x⁻¹ * y⁻¹) = 1 :=
  B.projection_commutator x y

/-- Named projection for the minimality certificate carried by Burnside data. -/
theorem dBMachin.generators_minimal {p : ℕ}
    {G : Type u} [Group G] (B : dBMachin p G) :
    minimalGeneratingSet G B.generators :=
  B.minimal_generators

@[simp] theorem dBMachin.min_gens_projection
    (p : ℕ) (G : Type u) [Group G] (hp : Nat.Prime p) (S : Set G)
    (hmin : minimalGeneratingSet G S) :
    (dBMachin.ofMinimalGenerators p G hp S hmin).projection =
      frattiniProjection p G := rfl


/-- Golod-Shafarevich framework data: generators, relators, positive depths, and
coefficient-counting functions used in the GS inequality. -/
structure gSFramew where
  Gen : Type u
  rels : relatorSet Gen
  depth : rels → ℕ
  depth_positive : ∀ r : rels, 0 < depth r
  finite_depth_fiber : ∀ n, Finite {r : rels // depth r = n}
  generatorWeight : Gen → ℕ
  generatorWeight_positive : ∀ g : Gen, 0 < generatorWeight g
  activeAt : ℕ → Set rels := fun n => {r | depth r ≤ n}
  active_spec : ∀ n r, r ∈ activeAt n ↔ depth r ≤ n
  relatorCount : ℕ → ℕ := fun n => Nat.card {r : rels // depth r = n}
  relatorCount_spec : ∀ n, relatorCount n = Nat.card {r : rels // depth r = n}


/-- Each exact-depth relator fiber is finite, so coefficient counts are genuine finite counts. -/
instance gSFramew.finiteDepthFiber
    (F : gSFramew.{u}) (n : ℕ) :
    Finite {r : F.rels // F.depth r = n} :=
  F.finite_depth_fiber n

/-- Named positivity accessor for relator depths in a GS framework. -/
theorem gSFramew.depth_pos (F : gSFramew.{u})
    (r : F.rels) : 0 < F.depth r :=
  F.depth_positive r

/-- Named positivity accessor for generator weights in a GS framework. -/
theorem gSFramew.generatorWeight_pos
    (F : gSFramew.{u}) (g : F.Gen) : 0 < F.generatorWeight g :=
  F.generatorWeight_positive g

/-- Named unfolding lemma for the relator-count function. -/
theorem gSFramew.relatorCount_eq
    (F : gSFramew.{u}) (n : ℕ) :
    F.relatorCount n = Nat.card {r : F.rels // F.depth r = n} :=
  F.relatorCount_spec n

/-- Active relators are monotone in the degree parameter. -/
theorem gSFramew.active_mono (F : gSFramew.{u})
    {m n : ℕ} (h : m ≤ n) : F.activeAt m ⊆ F.activeAt n := by
  intro r hr
  rw [F.active_spec] at hr ⊢
  exact Nat.le_trans hr h

/-- Every relator is active at its own depth. -/
theorem gSFramew.active_at_depth (F : gSFramew.{u})
    (r : F.rels) : r ∈ F.activeAt (F.depth r) := by
  rw [F.active_spec]


/-- Unfolded membership criterion for the active relator set. -/
theorem gSFramew.mem_active_iff
    (F : gSFramew.{u}) (n : ℕ) (r : F.rels) :
    r ∈ F.activeAt n ↔ F.depth r ≤ n := F.active_spec n r

/-- A relator is not active before its depth. -/
theorem gSFramew.not_memactive_ltdepth
    (F : gSFramew.{u}) {n : ℕ} {r : F.rels}
    (h : n < F.depth r) : r ∉ F.activeAt n := by
  intro hr
  have hle := (F.active_spec n r).1 hr
  omega

/-- No relator is active in degree zero, since all depths are positive. -/
theorem gSFramew.activeAt_zero
    (F : gSFramew.{u}) : F.activeAt 0 = ∅ := by
  ext r
  constructor
  · intro hr
    have hle := (F.active_spec 0 r).1 hr
    have hp := F.depth_positive r
    omega
  · intro hr
    cases hr

/-- Package for arithmetic/profinite applications of a GS framework, including a
realization map from the free group and a profinite topology on the target. -/
structure aPApplic where
  framework : gSFramew.{u}
  realization : Type u
  [group_realization : Group realization]
  eval : FreeGroup framework.Gen →* realization
  topology : pTopo realization
  /-- The free generators have dense image in the profinite realization. -/
  dense_image : bDense topology.topology (Set.range eval)
  relators_killed : ∀ r : framework.rels, eval r.1 = 1

attribute [instance] aPApplic.group_realization

/-- The evaluation map has dense image in the profinite realization. -/
theorem aPApplic.dense_range
    (A : aPApplic.{u}) :
    bDense A.topology.topology (Set.range A.eval) := A.dense_image

/-- Named accessor for the killed-relator condition in an arithmetic application. -/
@[simp] theorem aPApplic.eval_relator_eqone
    (A : aPApplic.{u}) (r : A.framework.rels) :
    A.eval r.1 = 1 :=
  A.relators_killed r


/-- The abstract group presented by a GS framework. -/
abbrev gSFramew.pGroup (F : gSFramew.{u}) : Type u :=
  quotientGroup (normalGeneratedRelators F.rels)

/-- In an arithmetic/profinite application, the normal closure of the relators is killed. -/
theorem aPApplic.normal_closure_kernel
    (A : aPApplic.{u}) :
    normalClosureRelators A.framework.rels ≤ MonoidHom.ker A.eval := by
  apply normal_closure_relators
  intro r hr
  change A.eval r = 1
  exact A.relators_killed ⟨r, hr⟩


/-- The generator images of a presentation in its presented group. -/
def presentationGeneratorSet (P : presentations.{u}) : Set P.Group :=
  Set.range P.of

/-- A minimal `p`-presentation: the displayed generator images minimally generate. -/
structure mPPres (p : ℕ) where
  pres : presentations.{u}
  prime : Nat.Prime p
  quotient_surjective : Function.Surjective pres.quotientMap
  relators_killed : ∀ r : pres.rels, pres.quotientMap r.1 = 1
  minimal : minimalGeneratingSet pres.Group (presentationGeneratorSet pres)
  generatorRank : Cardinal := Cardinal.mk pres.Gen

/-- Factor the realization map through the presented group of the framework. -/
noncomputable def aPApplic.factorMap
    (A : aPApplic.{u}) :
    A.framework.pGroup →* A.realization := by
  haveI : (normalClosureRelators A.framework.rels).Normal := Subgroup.normalClosure_normal
  refine QuotientGroup.lift (normalClosureRelators A.framework.rels) A.eval ?_
  intro x hx
  exact A.normal_closure_kernel hx


@[simp] theorem aPApplic.factorMap_mk
    (A : aPApplic.{u}) (x : FreeGroup A.framework.Gen) :
    A.factorMap
        (QuotientGroup.mk' (normalGeneratedRelators A.framework.rels).carrier x) =
      A.eval x := by
  haveI : (normalClosureRelators A.framework.rels).Normal := Subgroup.normalClosure_normal
  rfl

/-- If the realization map is onto, so is its factor through the presented group. -/
theorem aPApplic.factor_mapsurj_evalsurj
    (A : aPApplic.{u}) (h : Function.Surjective A.eval) :
    Function.Surjective A.factorMap := by
  intro y
  rcases h y with ⟨x, rfl⟩
  refine ⟨QuotientGroup.mk' (normalGeneratedRelators A.framework.rels).carrier x, ?_⟩
  simpa using A.factorMap_mk x

/-- The relator normal closure of a minimal presentation lies in the quotient kernel. -/
theorem mPPres.normal_closure_kernel {p : ℕ}
    (M : mPPres.{u} p) :
    normalClosureRelators M.pres.rels ≤ MonoidHom.ker M.pres.quotientMap := by
  apply normal_closure_relators
  intro r hr
  change M.pres.quotientMap r = 1
  exact M.relators_killed ⟨r, hr⟩

/-- The prime attached to a minimal p-presentation, as a named projection. -/
theorem mPPres.prime_p {p : ℕ} (M : mPPres.{u} p) :
    Nat.Prime p := M.prime

/-- A minimal p-presentation supplies the usual prime fact for its exponent. -/
@[reducible] def mPPres.fact_prime {p : ℕ}
    (M : mPPres.{u} p) : Fact p.Prime :=
  ⟨M.prime⟩

/-- The quotient map in a minimal presentation is surjective. -/
theorem mPPres.quotientMap_surjective {p : ℕ}
    (M : mPPres.{u} p) : Function.Surjective M.pres.quotientMap :=
  M.quotient_surjective

/-- Named accessor for the killed-relator condition in a minimal p-presentation. -/
@[simp] theorem mPPres.quotient_relator_one {p : ℕ}
    (M : mPPres.{u} p) (r : M.pres.rels) :
    M.pres.quotientMap r.1 = 1 :=
  M.relators_killed r

/-- Named accessor for the minimal generator certificate. -/
theorem mPPres.presentation_generators_minimal {p : ℕ}
    (M : mPPres.{u} p) :
    minimalGeneratingSet M.pres.Group (presentationGeneratorSet M.pres) :=
  M.minimal

/-- Bookkeeping attached to a minimal presentation, with positive relator depths
and the canonical killed-relator condition. -/
structure mPBookke (p : ℕ) where
  mpres : mPPres.{u} p
  depths : mpres.pres.rels → ℕ
  positive : ∀ r, 0 < depths r
  killed : ∀ r : mpres.pres.rels, mpres.pres.quotientMap r.1 = 1
  depthFiberFinite : ∀ n, Finite {r : mpres.pres.rels // depths r = n}
  killed_agrees : ∀ r, killed r = mpres.relators_killed r


/-- Relator depths in the bookkeeping package are positive. -/
theorem mPBookke.depth_pos {p : ℕ}
    (B : mPBookke.{u} p) (r : B.mpres.pres.rels) :
    0 < B.depths r := B.positive r

/-- The bookkeeping killed-relator proof agrees with the underlying presentation proof. -/
theorem mPBookke.killed_eq {p : ℕ}
    (B : mPBookke.{u} p) (r : B.mpres.pres.rels) :
    B.killed r = B.mpres.relators_killed r := B.killed_agrees r

/-- Each fixed-depth relator fiber is finite in the bookkeeping package. -/
theorem mPBookke.finite_depth_fiber {p : ℕ}
    (B : mPBookke.{u} p) (n : ℕ) :
    Finite {r : B.mpres.pres.rels // B.depths r = n} :=
  B.depthFiberFinite n

/-- The bookkeeping killed-relator proof, as an apply lemma. -/
@[simp] theorem mPBookke.killed_apply {p : ℕ}
    (B : mPBookke.{u} p) (r : B.mpres.pres.rels) :
    B.mpres.pres.quotientMap r.1 = 1 :=
  B.killed r

/-- The underlying minimal presentation in bookkeeping has prime parameter. -/
theorem mPBookke.prime {p : ℕ}
    (B : mPBookke.{u} p) : Nat.Prime p :=
  B.mpres.prime

/-- Minimal presentation bookkeeping supplies the usual prime fact for its exponent. -/
@[reducible] def mPBookke.fact_prime {p : ℕ}
    (B : mPBookke.{u} p) : Fact p.Prime :=
  ⟨B.mpres.prime⟩

/-- The underlying quotient map in bookkeeping is surjective. -/
theorem mPBookke.quotient_surjective {p : ℕ}
    (B : mPBookke.{u} p) :
    Function.Surjective B.mpres.pres.quotientMap :=
  B.mpres.quotient_surjective

/-- Quotient by a subgroup contained in the Frattini subgroup. -/
structure fKQuot (p : ℕ) (G : Type u) [Group G] where
  prime : Nat.Prime p
  kernel : nSubgro G
  le_frattini : kernel.carrier ≤ fSubgro p G
  projection : G →* quotientGroup kernel := QuotientGroup.mk' kernel.carrier
  projection_eq : projection = QuotientGroup.mk' kernel.carrier
  projection_surjective : Function.Surjective projection := by
    rw [projection_eq]
    exact QuotientGroup.mk'_surjective kernel.carrier
  /-- The quotient still maps canonically onto the Frattini quotient. -/
  factors_to_frattini : ∃ φ : quotientGroup kernel →* frattiniQuotient p G,
    φ.comp projection = QuotientGroup.mk' (fSubgro p G)

/-- The exponent of a Frattini-kernel quotient is prime. -/
theorem fKQuot.prime_p {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) : Nat.Prime p := Q.prime

/-- A Frattini-kernel quotient supplies the usual prime fact for its exponent. -/
@[reducible] def fKQuot.fact_prime {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) : Fact p.Prime :=
  ⟨Q.prime⟩

/-- The displayed projection is definitionally the quotient map, as a named lemma. -/
theorem fKQuot.projection_eq_mk {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) :
    Q.projection = QuotientGroup.mk' Q.kernel.carrier :=
  Q.projection_eq

/-- Accessor for the existence of a factor map to the Frattini quotient. -/
theorem fKQuot.exists_factor_fratt {p : ℕ}
    {G : Type u} [Group G] (Q : fKQuot p G) :
    ∃ φ : quotientGroup Q.kernel →* frattiniQuotient p G,
      φ.comp Q.projection = QuotientGroup.mk' (fSubgro p G) :=
  Q.factors_to_frattini

/-- The kernel of a Frattini-kernel quotient is contained in the Frattini subgroup. -/
theorem fKQuot.kernel_le_frattini {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) : Q.kernel.carrier ≤ fSubgro p G :=
  Q.le_frattini

/-- The displayed quotient projection is surjective. -/
theorem fKQuot.projection_surj {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) : Function.Surjective Q.projection :=
  Q.projection_surjective

/-- The canonical factor map from a Frattini-kernel quotient to the Frattini quotient. -/
noncomputable def fKQuot.factor {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) : quotientGroup Q.kernel →* frattiniQuotient p G :=
  quotientMapLE Q.kernel (frattiniNormalSubgroup p G) Q.le_frattini

@[simp] theorem fKQuot.factor_mk {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) (g : G) :
    Q.factor (QuotientGroup.mk' Q.kernel.carrier g) = frattiniProjection p G g := by
  simpa [fKQuot.factor, frattiniProjection]
    using quotient_mk Q.kernel (frattiniNormalSubgroup p G) Q.le_frattini g

/-- The canonical factor really composes with the quotient projection to the Frattini projection. -/
theorem fKQuot.factor_comp_projection {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) :
    Q.factor.comp Q.projection = frattiniProjection p G := by
  ext g
  rw [Q.projection_eq]
  exact Q.factor_mk g

/-- A basis-like family for degree one. -/
structure dOBasis (p : ℕ) (G : Type u) [Group G] where
  prime : Nat.Prime p
  index : Type v
  vector : index → frattiniQuotient p G
  spans : Subgroup.closure (Set.range vector) = ⊤
  minimal : ∀ T : Set (frattiniQuotient p G), T ⊂ Set.range vector →
    Subgroup.closure T ≠ ⊤
  injective : Function.Injective vector
  nontrivial : ∀ i, vector i ≠ 1

/-- The exponent of a degree-one basis is prime. -/
theorem dOBasis.prime_p {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) : Nat.Prime p := B.prime

/-- A degree-one basis package supplies the usual prime fact for its exponent. -/
@[reducible] def dOBasis.fact_prime {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) : Fact p.Prime :=
  ⟨B.prime⟩

/-- The cardinal rank represented by a degree-one basis. -/
noncomputable def dOBasis.rank {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) : Cardinal := Cardinal.mk B.index

/-- A degree-one basis gives an embedding into the Frattini quotient. -/
def dOBasis.embedding {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) : B.index ↪ frattiniQuotient p G where
  toFun := B.vector
  inj' := B.injective


/-- The canonical map from a Frattini-kernel quotient onto the Frattini quotient is surjective. -/
theorem fKQuot.factor_surjective {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) : Function.Surjective Q.factor :=
  of_le_surjective Q.kernel (frattiniNormalSubgroup p G) Q.le_frattini

/-- The displayed basis vector map as an embedding, pointwise. -/
@[simp] theorem dOBasis.embedding_apply {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) (i : B.index) : B.embedding i = B.vector i := rfl

/-- Basis vectors in degree one are nontrivial. -/
theorem dOBasis.vector_ne_one {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) (i : B.index) : B.vector i ≠ 1 :=
  B.nontrivial i

/-- The embedding associated to a degree-one basis is injective. -/
theorem dOBasis.embedding_injective {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) : Function.Injective B.embedding :=
  B.embedding.injective

/-- The range of the embedding is the range of the underlying vector map. -/
@[simp] theorem dOBasis.embedding_range {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) : Set.range B.embedding = Set.range B.vector := by
  rfl

/-- A degree-one basis spans the Frattini quotient. -/
theorem dOBasis.spans_top {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) :
    Subgroup.closure (Set.range B.vector) = ⊤ :=
  B.spans

/-- The vector map of a degree-one basis is injective. -/
theorem dOBasis.vector_injective {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) : Function.Injective B.vector :=
  B.injective

/-- Proper subfamilies of a degree-one basis do not span. -/
theorem dOBasis.not_span_ssubset {p : ℕ} {G : Type u} [Group G]
    (B : dOBasis p G) {T : Set (frattiniQuotient p G)}
    (hT : T ⊂ Set.range B.vector) : Subgroup.closure T ≠ ⊤ :=
  B.minimal T hT


end Group
end Submission

/-!
## Statements migrated from `Submission.Theorems`

These declarations keep their historical `Submission.Theorems` namespace while living
next to the API they describe.
-/

namespace Submission
namespace Theorems

open Submission.Group
open Submission.Algebra
open Submission.Topology

universe u v w x

/-- A concrete linear model for the mod-`p` Frattini quotient. -/
def FrattiniLinearModel {p : ℕ} (G : Type u) [Group G] : Prop :=
  ∃ V : eFSpace.{u} p,
    Nonempty (V.carrier ≃ₗ[ZMod p] Submission.mFAdditi p G)

lemma normal_closure_subset {A : Type u} [Group A]
    {s : Set A} {N : Subgroup A} (hN : N.Normal) (hs : s ⊆ N) :
    Subgroup.normalClosure s ≤ N := by
  letI : N.Normal := hN
  exact Subgroup.normalClosure_le_normal hs

lemma frattini_mk_pow {p : ℕ} {G : Type u} [Group G] (g : G) :
    ((QuotientGroup.mk' (Submission.Group.fSubgro p G)) g :
      Submission.Group.frattiniQuotient p G) ^ p = 1 := by
  have hmem : g ^ p ∈ Submission.Group.fSubgro p G := by
    change g ^ p ∈ Subgroup.normalClosure
      (Submission.Group.pPowers p G ∪ Submission.Group.commutators G)
    exact Subgroup.subset_normalClosure (by
      left
      exact ⟨g, rfl⟩)
  have hq :
      ((QuotientGroup.mk' (Submission.Group.fSubgro p G)) (g ^ p) :
        Submission.Group.frattiniQuotient p G) = 1 := by
    exact (QuotientGroup.eq_one_iff (N := Submission.Group.fSubgro p G)
      (g ^ p)).mpr hmem
  simpa [map_pow] using hq

lemma frattini_pow_one {p : ℕ} {G : Type u} [Group G]
    (x : Submission.Group.frattiniQuotient p G) :
    x ^ p = 1 := by
  refine Quotient.inductionOn x ?_
  intro g
  simpa using frattini_mk_pow (p := p) (G := G) g

lemma frattini_mk_comm {p : ℕ} {G : Type u} [Group G] (g h : G) :
    (((QuotientGroup.mk' (Submission.Group.fSubgro p G)) g) *
      ((QuotientGroup.mk' (Submission.Group.fSubgro p G)) h) *
      ((QuotientGroup.mk' (Submission.Group.fSubgro p G)) g)⁻¹ *
      ((QuotientGroup.mk' (Submission.Group.fSubgro p G)) h)⁻¹ :
      Submission.Group.frattiniQuotient p G) = 1 := by
  have hmem : g * h * g⁻¹ * h⁻¹ ∈ Submission.Group.fSubgro p G := by
    change g * h * g⁻¹ * h⁻¹ ∈
      Subgroup.normalClosure (Submission.Group.pPowers p G ∪ Submission.Group.commutators G)
    exact Subgroup.subset_normalClosure (by
      right
      exact ⟨(g, h), rfl⟩)
  have hq :
      ((QuotientGroup.mk' (Submission.Group.fSubgro p G)) (g * h * g⁻¹ * h⁻¹) :
        Submission.Group.frattiniQuotient p G) = 1 := by
    exact (QuotientGroup.eq_one_iff (N := Submission.Group.fSubgro p G)
      (g * h * g⁻¹ * h⁻¹)).mpr hmem
  simpa [map_mul, map_inv] using hq

lemma frattini_comm_one {p : ℕ} {G : Type u} [Group G]
    (x y : Submission.Group.frattiniQuotient p G) :
    x * y * x⁻¹ * y⁻¹ = 1 := by
  refine Quotient.inductionOn x ?_
  intro g
  refine Quotient.inductionOn y ?_
  intro h
  simpa using frattini_mk_comm (p := p) (G := G) g h

lemma frattini_subgroup_ker {p : ℕ}
    {A : Type u} {B : Type v} [Group A] [Group B]
    (φ : A →* Submission.Group.frattiniQuotient p B) :
    Submission.Group.fSubgro p A ≤ φ.ker := by
  change Subgroup.normalClosure (Submission.Group.pPowers p A ∪ Submission.Group.commutators A) ≤ φ.ker
  have hker : (φ.ker).Normal := by infer_instance
  refine normal_closure_subset hker ?_
  intro z hz
  rcases hz with hz | hz
  · rcases hz with ⟨a, rfl⟩
    change φ (a ^ p) = 1
    simpa [map_pow] using
      (frattini_pow_one (p := p) (G := B) (φ a))
  · rcases hz with ⟨ab, rfl⟩
    rcases ab with ⟨a, b⟩
    change φ (a * b * a⁻¹ * b⁻¹) = 1
    simpa [map_mul, map_inv] using
      (frattini_comm_one (p := p) (G := B) (φ a) (φ b))

/-- A convenient explicit maximality predicate for proper subgroups. -/
def MaximalSubgroup {G : Type u} [Group G] (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ ∀ K : Subgroup G, M < K → K = ⊤

lemma subgroup_nat_card {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} (h : H < K) :
    Nat.card H < Nat.card K := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype K := Fintype.ofFinite K
  let f : H → K := fun x => ⟨x.1, h.1 x.2⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (show (a : G) = b from congrArg (fun x : K => (x : G)) hab)
  have hnotle : ¬ K ≤ H := not_le_of_gt h
  have hex : ∃ g : G, g ∈ K ∧ g ∉ H := by
    by_contra hnone
    apply hnotle
    intro g hgK
    by_contra hgH
    exact hnone ⟨g, hgK, hgH⟩
  rcases hex with ⟨g, hgK, hgH⟩
  have hf_not_surj : ¬ Function.Surjective f := by
    intro hsurj
    rcases hsurj ⟨g, hgK⟩ with ⟨y, hy⟩
    apply hgH
    have hyval : (y : G) = g := by
      simpa [f] using congrArg Subtype.val hy
    simpa [hyval] using y.2
  have hcard : Fintype.card H < Fintype.card K :=
    Fintype.card_lt_of_injective_not_surjective f hf_inj hf_not_surj
  simpa [Nat.card_eq_fintype_card] using hcard

lemma maximal_subgroup {G : Type u} [Group G] [Finite G]
    {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ M : Subgroup G, H ≤ M ∧ MaximalSubgroup M := by
  classical
  letI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  let A : Finset (Subgroup G) := Finset.univ.filter (fun K => H ≤ K ∧ K ≠ ⊤)
  have hHmem : H ∈ A := by
    simp [A, hH]
  let B : Finset ℕ := A.image (fun K : Subgroup G => Nat.card K)
  have hBnon : B.Nonempty := by
    refine ⟨Nat.card H, ?_⟩
    exact Finset.mem_image.mpr ⟨H, hHmem, rfl⟩
  let m : ℕ := B.max' hBnon
  have hmB : m ∈ B := Finset.max'_mem B hBnon
  rcases Finset.mem_image.mp hmB with ⟨M, hMA, hMcard⟩
  have hMAprop : H ≤ M ∧ M ≠ ⊤ := by
    simpa [A] using hMA
  refine ⟨M, hMAprop.1, ?_⟩
  constructor
  · exact hMAprop.2
  · intro K hMK
    by_contra hKtop
    have hKmem : K ∈ A := by
      simp [A, hKtop, le_trans hMAprop.1 hMK.le]
    have hKcard_le : Nat.card K ≤ Nat.card M := by
      have hKB : Nat.card K ∈ B := Finset.mem_image.mpr ⟨K, hKmem, rfl⟩
      have hle : Nat.card K ≤ m := Finset.le_max' B (Nat.card K) hKB
      simpa [hMcard] using hle
    have hcard_lt : Nat.card M < Nat.card K :=
      subgroup_nat_card hMK
    exact (not_lt_of_ge hKcard_le) hcard_lt

lemma p_groups_group {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) : IsPGroup p G := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hG.1⟩
  haveI : Finite G := hG.2.1
  exact IsPGroup.iff_card.2 hG.2.2

lemma finite_pgroup_normalizer {p : ℕ} {G : Type u} [Group G] [Finite G]
    [Fact (Nat.Prime p)] (hPG : IsPGroup p G) {H : Subgroup G} (hH : H ≠ ⊤) :
    H < Subgroup.normalizer (H : Set G) := by
  classical
  have hHlt : H < ⊤ := lt_of_le_of_ne le_top hH
  haveI : Group.IsNilpotent G := hPG.isNilpotent
  exact Group.normalizerCondition_of_isNilpotent H hHlt

lemma maximal_normal_pgroup {p : ℕ} {G : Type u} [Group G]
    [Finite G] [Fact (Nat.Prime p)] (hPG : IsPGroup p G)
    {M : Subgroup G} (hM : MaximalSubgroup M) :
    M.Normal := by
  classical
  have hlt : M < Subgroup.normalizer (M : Set G) :=
    finite_pgroup_normalizer (p := p) hPG (H := M) hM.1
  have htop : Subgroup.normalizer (M : Set G) = ⊤ :=
    hM.2 (Subgroup.normalizer (M : Set G)) hlt
  exact (Subgroup.normalizer_eq_top_iff.mp htop)

lemma nontrivial_ne_top {G : Type u} [Group G]
    {M : Subgroup G} [M.Normal] (hM : M ≠ ⊤) :
    Nontrivial (G ⧸ M) := by
  classical
  have hnotall : ¬ ∀ g : G, g ∈ M := by
    intro hall
    apply hM
    apply eq_top_iff.mpr
    intro g hg
    exact hall g
  rcases not_forall.mp hnotall with ⟨g, hgM⟩
  have hne : (QuotientGroup.mk' M g : G ⧸ M) ≠ 1 := by
    intro h
    apply hgM
    exact (QuotientGroup.eq_one_iff g).mp h
  exact ⟨⟨QuotientGroup.mk' M g, 1, hne⟩⟩

lemma bot_or_maximal {G : Type u} [Group G]
    {M : Subgroup G} [M.Normal] (hM : MaximalSubgroup M) :
    ∀ L : Subgroup (G ⧸ M), L = ⊥ ∨ L = ⊤ := by
  classical
  intro L
  by_cases hLtop : L = ⊤
  · exact Or.inr hLtop
  · left
    let π : G →* G ⧸ M := QuotientGroup.mk' M
    have hMle : M ≤ Subgroup.comap π L := by
      intro g hg
      change π g ∈ L
      have hq : π g = 1 := by
        simpa [π, QuotientGroup.eq_one_iff] using hg
      simp [hq]
    have hcomap_ne_top : Subgroup.comap π L ≠ ⊤ := by
      intro htop
      apply hLtop
      apply eq_top_iff.mpr
      intro q hq
      rcases QuotientGroup.mk'_surjective M q with ⟨g, rfl⟩
      have hg : g ∈ Subgroup.comap π L := by
        rw [htop]
        trivial
      simpa [π] using hg
    have hcomap_eq : Subgroup.comap π L = M := by
      by_contra hne
      have hlt : M < Subgroup.comap π L := by
        exact lt_of_le_of_ne hMle (by intro hEq; exact hne hEq.symm)
      exact hcomap_ne_top (hM.2 (Subgroup.comap π L) hlt)
    apply le_antisymm
    · intro q hq
      rcases QuotientGroup.mk'_surjective M q with ⟨g, rfl⟩
      have hgcomap : g ∈ Subgroup.comap π L := hq
      have hgM : g ∈ M := by
        simpa [hcomap_eq] using hgcomap
      change π g = 1
      simpa [π, QuotientGroup.eq_one_iff] using hgM
    · exact bot_le

lemma order_prime_pgroup {p : ℕ} {Q : Type u} [Group Q]
    [Finite Q] [Nontrivial Q] [Fact (Nat.Prime p)] (hQ : IsPGroup p Q) :
    ∃ q : Q, orderOf q = p := by
  classical
  obtain ⟨n, hnpos, hn⟩ := hQ.nontrivial_iff_card.mp inferInstance
  have hpdiv : p ∣ Nat.card Q := by
    rw [hn]
    exact dvd_pow_self p hnpos.ne'
  exact exists_prime_orderOf_dvd_card' p hpdiv

lemma elementary_maximal_pgroup {p : ℕ} {G : Type u} [Group G]
    [Finite G] [Fact (Nat.Prime p)] (hPG : IsPGroup p G)
    {M : Subgroup G} [M.Normal] (hM : MaximalSubgroup M) :
    (∀ a b : G ⧸ M, a * b = b * a) ∧ (∀ a : G ⧸ M, a ^ p = 1) := by
  classical
  let Q := G ⧸ M
  haveI : Finite Q := inferInstance
  letI : Fintype Q := Fintype.ofFinite Q
  haveI : Nontrivial Q := nontrivial_ne_top hM.1
  have hQpg : IsPGroup p Q := hPG.to_quotient M
  rcases order_prime_pgroup (p := p) (Q := Q) hQpg with ⟨x, hx⟩
  have hno := bot_or_maximal (G := G) (M := M) hM
  have hx_ne_one : x ≠ 1 := by
    intro hx1
    have horder : orderOf x = 1 := by
      simp [hx1]
    have hp1 : p = 1 := by
      simpa [hx] using horder
    exact (Fact.out : Nat.Prime p).ne_one hp1
  have hcl_top : Subgroup.closure ({x} : Set Q) = ⊤ := by
    rcases hno (Subgroup.closure ({x} : Set Q)) with hbot | htop
    · exfalso
      have hxmem : x ∈ Subgroup.closure ({x} : Set Q) :=
        Subgroup.subset_closure (by simp)
      have hxbot : x ∈ (⊥ : Subgroup Q) := hbot ▸ hxmem
      have hxone : x = 1 := Subgroup.mem_bot.mp hxbot
      exact hx_ne_one hxone
    · exact htop
  have hmem_closure : ∀ y : Q, y ∈ Subgroup.closure ({x} : Set Q) := by
    intro y
    rw [hcl_top]
    trivial
  have hcomm_x : ∀ y : Q, Commute y x := by
    intro y
    refine Subgroup.closure_induction (k := ({x} : Set Q)) (p := fun z _ => Commute z x)
      ?_ ?_ ?_ ?_ (hmem_closure y)
    · intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact Commute.refl x
    · exact Commute.one_left x
    · intro a b ha hb hca hcb
      exact hca.mul_left hcb
    · intro a ha hca
      exact hca.inv_left
  have hcomm : ∀ y z : Q, y * z = z * y := by
    intro y z
    have hc : Commute y z := by
      refine Subgroup.closure_induction (k := ({x} : Set Q)) (p := fun t _ => Commute y t)
        ?_ ?_ ?_ ?_ (hmem_closure z)
      · intro t ht
        simp only [Set.mem_singleton_iff] at ht
        subst t
        exact hcomm_x y
      · exact Commute.one_right y
      · intro a b ha hb hca hcb
        exact hca.mul_right hcb
      · intro a ha hca
        exact hca.inv_right
    exact hc.eq
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := hcomm }
  have hxpow : x ^ p = 1 := by
    simpa [hx] using (pow_orderOf_eq_one x)
  have hexp : ∀ y : Q, y ^ p = 1 := by
    intro y
    refine Subgroup.closure_induction (k := ({x} : Set Q)) (p := fun z _ => z ^ p = 1)
      ?_ ?_ ?_ ?_ (hmem_closure y)
    · intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      exact hxpow
    · simp
    · intro a b ha hb hpa hpb
      simp [mul_pow, hpa, hpb]
    · intro a ha hpa
      simpa [inv_pow] using congrArg Inv.inv hpa
  exact ⟨hcomm, hexp⟩

lemma maximal_contains_abelianization {p : ℕ} {G : Type u} [Group G]
    [Finite G] [Fact (Nat.Prime p)] (hPG : IsPGroup p G)
    {M : Subgroup G} (hM : MaximalSubgroup M) :
    mAKern p G ≤ M := by
  classical
  have hMnormal : M.Normal :=
    maximal_normal_pgroup (p := p) hPG (M := M) hM
  letI : M.Normal := hMnormal
  rcases elementary_maximal_pgroup (p := p) hPG (G := G) (M := M) hM with
    ⟨hcomm, hexp⟩
  letI : CommGroup (G ⧸ M) := { (inferInstance : Group (G ⧸ M)) with
    mul_comm := hcomm }
  rw [mAKern]
  have hsubset : (pPowers p G ∪ commutators G) ⊆ (M : Set G) := by
    intro y hy
    rcases hy with hy | hy
    · rcases hy with ⟨g, rfl⟩
      have hq : (QuotientGroup.mk' M (g ^ p) : G ⧸ M) = 1 := by
        simpa using (hexp (QuotientGroup.mk' M g))
      exact (QuotientGroup.eq_one_iff (g ^ p)).mp hq
    · rcases hy with ⟨q, rfl⟩
      rcases q with ⟨a, b⟩
      have hq :
          (QuotientGroup.mk' M (a * b * a⁻¹ * b⁻¹) : G ⧸ M) = 1 := by
        simp [mul_assoc]
      exact (QuotientGroup.eq_one_iff (a * b * a⁻¹ * b⁻¹)).mp hq
  exact Subgroup.normalClosure_le_normal hsubset

section AdditiveMultiplicative

variable {A : Type u}

def mulImageEquiv (S : Set A) :
    S ≃ (Additive.ofMul '' S : Set (Additive A)) where
  toFun s := ⟨Additive.ofMul s.1, ⟨s.1, s.2, rfl⟩⟩
  invFun t := ⟨Additive.toMul t.1, by
    rcases t.2 with ⟨a, ha, rfl⟩
    simpa using ha⟩
  left_inv s := by
    ext
    rfl
  right_inv t := by
    rcases t with ⟨x, hx⟩
    rcases hx with ⟨a, ha, rfl⟩
    ext
    rfl

def mulImage (T : Set (Additive A)) :
    T ≃ (Additive.toMul '' T : Set A) where
  toFun t := ⟨Additive.toMul t.1, ⟨t.1, t.2, rfl⟩⟩
  invFun s := ⟨Additive.ofMul s.1, by
    rcases s.2 with ⟨x, hx, rfl⟩
    simpa using hx⟩
  left_inv t := by
    ext
    rfl
  right_inv s := by
    rcases s with ⟨a, ha⟩
    rcases ha with ⟨x, hx, rfl⟩
    ext
    rfl

lemma cardinal_mul_image (S : Set A) :
    Cardinal.mk (Additive.ofMul '' S : Set (Additive A)) = Cardinal.mk S :=
  Cardinal.mk_congr (mulImageEquiv S).symm

lemma cardinal_mk_mul (T : Set (Additive A)) :
    Cardinal.mk (Additive.toMul '' T : Set A) = Cardinal.mk T :=
  Cardinal.mk_congr (mulImage T).symm

end AdditiveMultiplicative

section SpanClosure

variable {p : ℕ} {A : Type u} [CommGroup A]

lemma mul_cast_smul [Module (ZMod p) (Additive A)] (n : ℕ) (x : Additive A) :
    Additive.toMul (((n : ZMod p) • x : Additive A)) = (Additive.toMul x) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hsmul :
          (((Nat.succ n : ℕ) : ZMod p) • x : Additive A) =
            ((n : ZMod p) • x + x) := by
        simp [Nat.cast_succ, add_smul]
      rw [hsmul]
      simp [ih, pow_succ]

lemma mul_span_closure [Module (ZMod p) (Additive A)]
    (S : Set A) {a : A} (ha : a ∈ Subgroup.closure S) :
    Additive.ofMul a ∈ Submodule.span (ZMod p) (Additive.ofMul '' S) := by
  let W : Submodule (ZMod p) (Additive A) :=
    Submodule.span (ZMod p) (Additive.ofMul '' S)
  let H : Subgroup A :=
    { carrier := {a : A | Additive.ofMul a ∈ W}
      one_mem' := by
        change Additive.ofMul (1 : A) ∈ W
        simp
      mul_mem' := by
        intro x y hx hy
        change Additive.ofMul (x * y) ∈ W
        simpa using W.add_mem hx hy
      inv_mem' := by
        intro x hx
        change Additive.ofMul x⁻¹ ∈ W
        simpa using W.neg_mem hx }
  have hle : Subgroup.closure S ≤ H := by
    refine (Subgroup.closure_le H).2 ?_
    intro x hx
    change Additive.ofMul x ∈ W
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  change a ∈ H
  exact hle ha

lemma span_top_closure [Module (ZMod p) (Additive A)]
    {S : Set A} (hS : Subgroup.closure S = ⊤) :
    Submodule.span (ZMod p) (Additive.ofMul '' S) = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro x hx
    induction x using Additive.rec with
    | ofMul a =>
        exact mul_span_closure (p := p) (S := S) (a := a) (by
          simp [hS])

lemma mul_closure_span [NeZero p] [Module (ZMod p) (Additive A)]
    (S : Set A) {x : Additive A}
    (hx : x ∈ Submodule.span (ZMod p) (Additive.ofMul '' S)) :
    Additive.toMul x ∈ Subgroup.closure S := by
  let H : Subgroup A := Subgroup.closure S
  let W : Submodule (ZMod p) (Additive A) :=
    { carrier := {x : Additive A | Additive.toMul x ∈ H}
      zero_mem' := by
        change (1 : A) ∈ H
        exact H.one_mem
      add_mem' := by
        intro x y hx hy
        change Additive.toMul (x + y) ∈ H
        simpa using H.mul_mem hx hy
      smul_mem' := by
        intro r x hx
        change Additive.toMul (r • x) ∈ H
        have hr : ((r.val : ℕ) : ZMod p) = r := ZMod.natCast_zmod_val r
        rw [← hr]
        rw [mul_cast_smul (p := p) (A := A) r.val x]
        exact H.pow_mem hx r.val }
  have hle : Submodule.span (ZMod p) (Additive.ofMul '' S) ≤ W := by
    refine Submodule.span_le.2 ?_
    intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    change a ∈ H
    exact Subgroup.subset_closure ha
  change x ∈ W
  exact hle hx

lemma closure_top_span [NeZero p] [Module (ZMod p) (Additive A)]
    {S : Set A}
    (hS : Submodule.span (ZMod p) (Additive.ofMul '' S) = ⊤) :
    Subgroup.closure S = ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro a ha
    have hx : Additive.ofMul a ∈ Submodule.span (ZMod p) (Additive.ofMul '' S) := by
      rw [hS]
      trivial
    simpa using mul_closure_span (p := p) (S := S) hx

end SpanClosure

lemma additive_spanning_rank (p : ℕ) [Fact p.Prime]
    (M : Type u) [AddCommGroup M] [Module (ZMod p) M] :
    ∃ T : Set M, Submodule.span (ZMod p) T = ⊤ ∧
      Cardinal.mk T = Module.rank (ZMod p) M := by
  classical
  let ι := Module.Basis.ofVectorSpaceIndex (ZMod p) M
  let b : Module.Basis ι (ZMod p) M := Module.Basis.ofVectorSpace (ZMod p) M
  let T : Set M := Set.range b
  refine ⟨T, ?_, ?_⟩
  · change Submodule.span (ZMod p) (Set.range b) = ⊤
    exact b.span_eq
  · let e : ι ≃ T :=
      Equiv.ofBijective
        (fun i : ι => (⟨b i, ⟨i, rfl⟩⟩ : T))
        (by
          constructor
          · intro i j hij
            exact b.injective (Subtype.ext_iff.mp hij)
          · intro y
            rcases y with ⟨m, ⟨i, rfl⟩⟩
            exact ⟨i, rfl⟩)
    have hmkT : Cardinal.mk T = Cardinal.mk ι := Cardinal.mk_congr e.symm
    have hmkι : Cardinal.mk ι = Module.rank (ZMod p) M := by
      simpa using (b.mk_eq_rank)
    exact hmkT.trans hmkι

theorem multiplicative_generator_rank (p : ℕ) [Fact p.Prime] [NeZero p]
    (A : Type u) [CommGroup A] [Module (ZMod p) (Additive A)] :
    sInf {c : Cardinal | ∃ S : Set A,
      Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c}
      = Module.rank (ZMod p) (Additive A) := by
  classical
  apply le_antisymm
  · have hmem : Module.rank (ZMod p) (Additive A) ∈
        {c : Cardinal | ∃ S : Set A,
          Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c} := by
      obtain ⟨T, hspanT, hcardT⟩ :=
        additive_spanning_rank (p := p) (M := Additive A)
      let S : Set A := Additive.toMul '' T
      refine ⟨S, ?_, ?_⟩
      · apply closure_top_span (p := p) (S := S)
        have himage : Additive.ofMul '' S = T := by
          ext x
          constructor
          · rintro ⟨a, ha, rfl⟩
            rcases ha with ⟨y, hy, rfl⟩
            simpa using hy
          · intro hx
            exact ⟨Additive.toMul x, ⟨x, hx, rfl⟩, by simp⟩
        simpa [himage] using hspanT
      · have hcardS : Cardinal.mk S = Cardinal.mk T := by
          simpa [S] using cardinal_mk_mul (A := A) T
        exact hcardS.trans hcardT
    exact csInf_le ⟨0, fun _ _ => bot_le⟩ hmem
  · refine le_csInf ?_ ?_
    · obtain ⟨T, hspanT, hcardT⟩ :=
        additive_spanning_rank (p := p) (M := Additive A)
      let S : Set A := Additive.toMul '' T
      refine ⟨Module.rank (ZMod p) (Additive A), S, ?_, ?_⟩
      · apply closure_top_span (p := p) (S := S)
        have himage : Additive.ofMul '' S = T := by
          ext x
          constructor
          · rintro ⟨a, ha, rfl⟩
            rcases ha with ⟨y, hy, rfl⟩
            simpa using hy
          · intro hx
            exact ⟨Additive.toMul x, ⟨x, hx, rfl⟩, by simp⟩
        simpa [himage] using hspanT
      · have hcardS : Cardinal.mk S = Cardinal.mk T := by
          simpa [S] using cardinal_mk_mul (A := A) T
        exact hcardS.trans hcardT
    intro c hc
    rcases hc with ⟨S, hgen, hcard⟩
    have hspan :
        Submodule.span (ZMod p) (Additive.ofMul '' S : Set (Additive A)) = ⊤ :=
      span_top_closure (p := p) (S := S) hgen
    have hrank_le :
        Module.rank (ZMod p) (Additive A) ≤
          Cardinal.mk (Additive.ofMul '' S : Set (Additive A)) := by
      calc
        Module.rank (ZMod p) (Additive A)
            = Module.rank (ZMod p)
                (Submodule.span (ZMod p) (Additive.ofMul '' S : Set (Additive A))) := by
              rw [hspan, rank_top]
        _ ≤ Cardinal.mk (Additive.ofMul '' S : Set (Additive A)) :=
              rank_span_le (R := ZMod p)
                (M := Additive A)
                (Additive.ofMul '' S : Set (Additive A))
    have hcardImage :
        Cardinal.mk (Additive.ofMul '' S : Set (Additive A)) = Cardinal.mk S :=
      cardinal_mul_image (A := A) S
    calc
      Module.rank (ZMod p) (Additive A)
          ≤ Cardinal.mk (Additive.ofMul '' S : Set (Additive A)) := hrank_le
      _ = Cardinal.mk S := hcardImage
      _ = c := hcard

lemma commutator_word {G : Type u} [Group G] (a b : G) :
    a * b * a⁻¹ * b⁻¹ ∈ _root_.commutator G := by
  change ⁅a, b⁆ ∈ _root_.commutator G
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)

def mulEquivImage {A B : Type u} [Mul A] [Mul B] (e : A ≃* B) (S : Set A) :
    S ≃ (e '' S : Set B) where
  toFun s := ⟨e s.1, ⟨s.1, s.2, rfl⟩⟩
  invFun t := ⟨e.symm t.1, by
    rcases t.2 with ⟨a, ha, ht⟩
    rw [← ht]
    simpa using ha⟩
  left_inv s := by
    ext
    simp
  right_inv t := by
    ext
    simp

lemma cardinal_mk_image {A B : Type u} [Mul A] [Mul B]
    (e : A ≃* B) (S : Set A) :
    Cardinal.mk (e '' S : Set B) = Cardinal.mk S :=
  Cardinal.mk_congr (mulEquivImage e S).symm

lemma closure_image_top {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) {S : Set A} (hS : Subgroup.closure S = ⊤) :
    Subgroup.closure (e '' S : Set B) = ⊤ := by
  calc
    Subgroup.closure (e '' S : Set B)
        = Subgroup.map e.toMonoidHom (Subgroup.closure S) :=
          (MonoidHom.map_closure e.toMonoidHom S).symm
    _ = ⊤ := by
      rw [hS]
      exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective

lemma multiplicative_inf_congr {A B : Type u} [Group A] [Group B]
    (e : A ≃* B) :
    sInf {c : Cardinal | ∃ S : Set A,
      Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c}
      =
    sInf {c : Cardinal | ∃ T : Set B,
      Subgroup.closure T = ⊤ ∧ Cardinal.mk T = c} := by
  classical
  congr 1
  ext c
  constructor
  · rintro ⟨S, hS, hcard⟩
    refine ⟨e '' S, closure_image_top e hS, ?_⟩
    exact (cardinal_mk_image e S).trans hcard
  · rintro ⟨T, hT, hcard⟩
    refine ⟨e.symm '' T, closure_image_top e.symm hT, ?_⟩
    exact (cardinal_mk_image e.symm T).trans hcard

lemma frattini_mod_p {p : ℕ} {G : Type u} [Group G] :
    Submission.Group.fSubgro p G = Submission.modPFrattini p G := by
  apply le_antisymm
  · dsimp [Submission.Group.fSubgro, Submission.Group.mAKern]
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    rcases hx with hp | hc
    · exact (le_sup_left : Submission.pPowerSubgroup p G ≤ Submission.modPFrattini p G) (by
        dsimp [Submission.pPowerSubgroup, Submission.Group.pPowers] at hp ⊢
        exact Subgroup.subset_normalClosure hp)
    · dsimp [Submission.Group.commutators] at hc
      rcases hc with ⟨ab, rfl⟩
      rcases ab with ⟨a, b⟩
      exact (le_sup_right : _root_.commutator G ≤ Submission.modPFrattini p G)
        (commutator_word (a := a) (b := b))
  · dsimp [Submission.modPFrattini]
    refine sup_le ?hp ?hc
    · dsimp [Submission.pPowerSubgroup]
      refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      dsimp [Submission.Group.fSubgro, Submission.Group.mAKern]
      exact Subgroup.subset_normalClosure (by
        left
        simpa [Submission.Group.pPowers] using hx)
    · rw [_root_.commutator_def]
      refine (Subgroup.commutator_le).2 ?_
      intro a ha b hb
      dsimp [Submission.Group.fSubgro, Submission.Group.mAKern]
      exact Subgroup.subset_normalClosure (by
        right
        change ⁅a, b⁆ ∈ Submission.Group.commutators G
        change (a * b * a⁻¹ * b⁻¹) ∈ Submission.Group.commutators G
        exact ⟨(a, b), rfl⟩)

lemma nsmul_mod_exponent {p : ℕ} {A : Type*} [AddCommGroup A]
    (hexp : ∀ a : A, p • a = 0) (n : ℕ) (a : A) :
    (n % p) • a = n • a := by
  calc
    (n % p) • a = 0 + (n % p) • a := by simp
    _ = (p * (n / p)) • a + (n % p) • a := by
      rw [mul_nsmul, hexp, nsmul_zero]
    _ = (p * (n / p) + n % p) • a := (add_nsmul a (p * (n / p)) (n % p)).symm
    _ = n • a := by rw [Nat.div_add_mod]

lemma nsmul_zmod {p : ℕ} [NeZero p] {A : Type*} [AddCommGroup A]
    (hexp : ∀ a : A, p • a = 0) {m n : ℕ}
    (h : (m : ZMod p) = (n : ZMod p)) (a : A) :
    m • a = n • a := by
  have hmod : m % p = n % p := by
    have hv := congrArg (fun z : ZMod p => z.val) h
    simpa using hv
  calc
    m • a = (m % p) • a := (nsmul_mod_exponent hexp m a).symm
    _ = (n % p) • a := by rw [hmod]
    _ = n • a := nsmul_mod_exponent hexp n a

@[reducible] def zmodModuleExponent {p : ℕ} [NeZero p] (A : Type*) [AddCommGroup A]
    (hexp : ∀ a : A, p • a = 0) : Module (ZMod p) A where
  smul z a := z.val • a
  one_smul := by
    intro a
    change ((1 : ZMod p).val) • a = a
    have hcast : ((((1 : ZMod p).val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p)) := by
      simp
    simpa using
      (nsmul_zmod (p := p) (A := A) hexp
        (m := (1 : ZMod p).val) (n := 1) hcast a)
  mul_smul := by
    intro z w a
    change ((z * w).val) • a = z.val • (w.val • a)
    have hcast :
        ((((z * w).val : ℕ) : ZMod p) =
          (((z.val * w.val : ℕ) : ZMod p))) := by
      simp [Nat.cast_mul]
    calc
      ((z * w).val) • a = (z.val * w.val) • a :=
        nsmul_zmod (p := p) (A := A) hexp hcast a
      _ = z.val • (w.val • a) := by rw [Nat.mul_comm, mul_nsmul]
  zero_smul := by
    intro a
    change ((0 : ZMod p).val) • a = 0
    simp
  add_smul := by
    intro z w a
    change ((z + w).val) • a = z.val • a + w.val • a
    have hcast :
        ((((z + w).val : ℕ) : ZMod p) =
          (((z.val + w.val : ℕ) : ZMod p))) := by
      simp [Nat.cast_add]
    calc
      ((z + w).val) • a = (z.val + w.val) • a :=
        nsmul_zmod (p := p) (A := A) hexp hcast a
      _ = z.val • a + w.val • a := by rw [add_nsmul]
  smul_zero := by
    intro z
    change z.val • (0 : A) = 0
    simp
  smul_add := by
    intro z a b
    change z.val • (a + b) = z.val • a + z.val • b
    rw [nsmul_add]

def trivSqFst (R M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    TrivSqZeroExt R M →ₐ[R] R :=
  TrivSqZeroExt.fstHom R R M

lemma frattini_zassenhaus_two {p : ℕ} {G : Type u} [Group G]
    (_hp : Nat.Prime p) :
    Submission.Group.fSubgro p G ≤ GroupAlgebra.zSubgro p G 2 := by
  classical
  haveI : (GroupAlgebra.zSubgro p G 2).Normal := by infer_instance
  dsimp [Submission.Group.fSubgro, Submission.Group.mAKern]
  refine Subgroup.normalClosure_le_normal ?_
  rintro x (⟨g, rfl⟩ | ⟨⟨a, b⟩, rfl⟩)
  · exact GroupAlgebra.pow_subgroup_two p G g
  · change ⁅a, b⁆ ∈ GroupAlgebra.zSubgro p G 2
    exact GroupAlgebra.commutator_subgroup_two p G a b

set_option maxHeartbeats 4000000 in
-- isDefEq, whnf?
lemma zassenhaus_frattini {p : ℕ} {G : Type u} [Group G]
    (hp : Nat.Prime p) :
    GroupAlgebra.zSubgro p G 2 ≤ Submission.Group.fSubgro p G := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro g hg
  let k := ZMod p
  let N : Subgroup G := Submission.Group.fSubgro p G
  haveI : N.Normal := by
    dsimp [N, Submission.Group.fSubgro, Submission.Group.mAKern]
    infer_instance
  let Q := G ⧸ N
  have hcommQ : ∀ q r : Q, q * r = r * q := by
    intro q r
    refine QuotientGroup.induction_on q ?_
    intro a
    refine QuotientGroup.induction_on r ?_
    intro b
    have hc_mem : a * b * a⁻¹ * b⁻¹ ∈ N := by
      dsimp [N, Submission.Group.fSubgro, Submission.Group.mAKern]
      exact Subgroup.subset_normalClosure (by
        right
        exact ⟨(a, b), rfl⟩)
    have hc : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : Q) = 1 :=
      (QuotientGroup.eq_one_iff (N := N) (a * b * a⁻¹ * b⁻¹)).mpr hc_mem
    have hc' :
        (QuotientGroup.mk a : Q) * QuotientGroup.mk b *
            (QuotientGroup.mk a : Q)⁻¹ * (QuotientGroup.mk b : Q)⁻¹ = 1 := by
      simpa using hc
    calc
      (QuotientGroup.mk a : Q) * QuotientGroup.mk b =
          (((QuotientGroup.mk a : Q) * QuotientGroup.mk b *
              (QuotientGroup.mk a : Q)⁻¹ * (QuotientGroup.mk b : Q)⁻¹) *
            ((QuotientGroup.mk b : Q) * QuotientGroup.mk a)) := by
            group
      _ = 1 * ((QuotientGroup.mk b : Q) * QuotientGroup.mk a) := by rw [hc']
      _ = (QuotientGroup.mk b : Q) * QuotientGroup.mk a := by simp
  letI : CommGroup Q := { (inferInstance : Group Q) with
    mul_comm := hcommQ }
  have hpowQ : ∀ q : Q, q ^ p = 1 := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro a
    have hp_mem : a ^ p ∈ N := by
      dsimp [N, Submission.Group.fSubgro, Submission.Group.mAKern]
      exact Subgroup.subset_normalClosure (by
        left
        exact ⟨a, rfl⟩)
    have hmk : (QuotientGroup.mk (a ^ p) : Q) = 1 :=
      (QuotientGroup.eq_one_iff (N := N) (a ^ p)).mpr hp_mem
    simpa using hmk
  have hexpA : ∀ a : Additive Q, p • a = 0 := by
    intro a
    change Additive.ofMul ((Additive.toMul a) ^ p) = (0 : Additive Q)
    simpa using congrArg Additive.ofMul (hpowQ (Additive.toMul a))
  letI : Module k (Additive Q) :=
    zmodModuleExponent (p := p) (A := Additive Q) hexpA
  letI : Module kᵐᵒᵖ (Additive Q) :=
    Module.compHom (Additive Q)
      (RingHom.fromOpposite (RingHom.id k) (by intro x y; exact Commute.all x y))
  haveI : IsCentralScalar k (Additive Q) := by
    refine ⟨?_⟩
    intro r a
    rfl
  let D := TrivSqZeroExt k (Additive Q)
  let π : D →ₐ[k] k := trivSqFst k (Additive Q)
  let ρ : G →* D :=
  { toFun := fun a => (⟨1, Additive.ofMul (QuotientGroup.mk a : Q)⟩ : D)
    map_one' := by
      ext <;> simp
    map_mul' := by
      intro a b
      ext
      · change (1 : k) = (1 : k) * (1 : k)
        simp
      · change (QuotientGroup.mk (a * b) : Q) =
          Additive.toMul
            ((1 : k) • Additive.ofMul (QuotientGroup.mk b : Q) +
              (MulOpposite.op (1 : k)) • Additive.ofMul (QuotientGroup.mk a : Q))
        simpa using hcommQ (QuotientGroup.mk a : Q) (QuotientGroup.mk b : Q) }
  let F : MonoidAlgebra k G →ₐ[k] D :=
    _root_.MonoidAlgebra.lift k D G ρ
  have hπF : π.comp F = GroupAlgebra.augmentation k G := by
    ext a
    simp [F, ρ, π, GroupAlgebra.augmentation, GroupAlgebra.trivialCharacter,
      trivSqFst, TrivSqZeroExt.fstHom]
  have hπF_apply : ∀ z : MonoidAlgebra k G, π (F z) = GroupAlgebra.augmentation k G z := by
    intro z
    have hz := congrArg (fun H : MonoidAlgebra k G →ₐ[k] k => H z) hπF
    simpa using hz
  have hsq : ∀ u v : D, π u = 0 → π v = 0 → u * v = 0 := by
    intro u v hu hv
    have hu' : u.fst = 0 := by simpa [π, trivSqFst] using hu
    have hv' : v.fst = 0 := by simpa [π, trivSqFst] using hv
    ext
    · rw [TrivSqZeroExt.fst_mul, hu', hv', zero_mul]
      simp
    · rw [TrivSqZeroExt.snd_mul, hu', hv']
      simp
  have hkill :
      ∀ {z : MonoidAlgebra k G},
        z ∈ GroupAlgebra.augmentationPower k G 2 → F z = 0 := by
    intro z hz
    let I : Ideal (MonoidAlgebra k G) := GroupAlgebra.augmentationIdeal k G
    haveI : I.IsTwoSided := by
      dsimp [I, GroupAlgebra.augmentationIdeal]
      infer_instance
    have hle : I * I ≤ RingHom.ker F.toRingHom := by
      rw [Ideal.mul_le]
      intro a ha b hb
      change F (a * b) = 0
      rw [map_mul]
      have ha0 : GroupAlgebra.augmentation k G a = 0 := by
        simpa [I, GroupAlgebra.augmentationIdeal] using ha
      have hb0 : GroupAlgebra.augmentation k G b = 0 := by
        simpa [I, GroupAlgebra.augmentationIdeal] using hb
      have hFa : π (F a) = 0 := by
        calc
          π (F a) = GroupAlgebra.augmentation k G a := hπF_apply a
          _ = 0 := ha0
      have hFb : π (F b) = 0 := by
        calc
          π (F b) = GroupAlgebra.augmentation k G b := hπF_apply b
          _ = 0 := hb0
      exact hsq (F a) (F b) hFa hFb
    have hz' : z ∈ I * I := by
      have hz0 : z ∈ I ^ 2 := by
        simpa [I, GroupAlgebra.augmentationPower] using hz
      rw [show I ^ 2 = I * I by rw [Ideal.IsTwoSided.pow_succ, Submodule.pow_one]] at hz0
      exact hz0
    exact hle hz'
  have hmem :
      (_root_.MonoidAlgebra.of k G g - 1 : MonoidAlgebra k G) ∈
        GroupAlgebra.augmentationPower k G 2 := by
    simpa [k, GroupAlgebra.zSubgro] using hg
  have hzero : F (_root_.MonoidAlgebra.of k G g - 1 : MonoidAlgebra k G) = 0 :=
    hkill hmem
  have hFval :
      F (_root_.MonoidAlgebra.of k G g - 1 : MonoidAlgebra k G) =
        (⟨0, Additive.ofMul (QuotientGroup.mk g : Q)⟩ : D) := by
    rw [map_sub]
    have hFof : F (_root_.MonoidAlgebra.of k G g) =
        (⟨1, Additive.ofMul (QuotientGroup.mk g : Q)⟩ : D) := by
      simp [F, ρ]
    rw [hFof, map_one]
    ext
    · change (1 : k) - 1 = 0
      simp
    · change Additive.toMul (Additive.ofMul (QuotientGroup.mk g : Q) - 0) =
        QuotientGroup.mk g
      simp
  have hpairzero :
      (⟨0, Additive.ofMul (QuotientGroup.mk g : Q)⟩ : D) = 0 := by
    rw [hFval] at hzero
    exact hzero
  have hqadd : Additive.ofMul (QuotientGroup.mk g : Q) = 0 := by
    have hsnd := congrArg (fun z : D => z.snd) hpairzero
    simpa only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_zero] using hsnd
  have hq : (QuotientGroup.mk g : Q) = 1 := by
    have hmul := congrArg Additive.toMul hqadd
    exact hmul
  simpa [N] using ((QuotientGroup.eq_one_iff (N := N) g).mp hq)
/-- The second Zassenhaus term is generated by p-powers and commutators. -/
theorem secondTermFormula {p : ℕ} {G : Type u} [Group G] [Fact p.Prime]
    (hstandard : GroupAlgebra.zSubgro p G 2 = zFTerm p 2 G)
    (hdegreeTwo : zFTerm p 2 G = pPowerSubgroup p G ⊔ commutatorSubgroup G) :
    GroupAlgebra.zSubgro p G 2 = pPowerSubgroup p G ⊔ commutatorSubgroup G
  := by
  exact hstandard.trans hdegreeTwo
/-- The Frattini subgroup of a finite p-group is generated by p-powers and commutators. -/
theorem frattiniFormulaGroups {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) :
    _root_.frattini G = pPowerSubgroup p G ⊔ commutatorSubgroup G
  := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hG.1⟩
  haveI : Finite G := hG.finite
  have hPG : IsPGroup p G := p_groups_group (p := p) (G := G) hG
  let N : Subgroup G := Submission.Group.fSubgro p G
  let Q : Type u := Submission.Group.frattiniQuotient p G
  have hcommQ : ∀ x y : Q, x * y = y * x := by
    intro x y
    rw [← commutatorElement_eq_one_iff_mul_comm]
    change x * y * x⁻¹ * y⁻¹ = 1
    exact frattini_comm_one (p := p) (G := G) x y
  have hPhiQ_bot : _root_.frattini Q = ⊥ := by
    letI : CommGroup Q := { (inferInstance : Group Q) with
      mul_comm := hcommQ }
    have hexpA : ∀ a : Additive Q, p • a = 0 := by
      intro a
      change Additive.ofMul ((Additive.toMul a) ^ p) = (0 : Additive Q)
      simpa using congrArg Additive.ofMul
        (frattini_pow_one (p := p) (G := G) (Additive.toMul a))
    letI : Module (ZMod p) (Additive Q) :=
      AddCommGroup.zmodModule (n := p) hexpA
    apply le_bot_iff.mp
    intro q hq
    rw [Subgroup.mem_bot]
    by_contra hq_ne
    let v : Additive Q := Additive.ofMul q
    have hv_not_bot : v ∉ (⊥ : Submodule (ZMod p) (Additive Q)) := by
      simpa [v, ofMul_eq_zero] using hq_ne
    rcases Submodule.exists_le_ker_of_notMem (K := ZMod p) (V := Additive Q)
        (p := (⊥ : Submodule (ZMod p) (Additive Q))) hv_not_bot with
      ⟨f, hfv_ne, _hbot_le⟩
    have hf_surj : Function.Surjective f := by
      intro y
      refine ⟨(y * (f v)⁻¹) • v, ?_⟩
      rw [map_smul]
      change (y * (f v)⁻¹) * f v = y
      rw [mul_assoc, inv_mul_cancel₀ hfv_ne, mul_one]
    have hbotCoatom : IsCoatom (⊥ : Submodule (ZMod p) (ZMod p)) := by
      constructor
      · exact bot_ne_top
      · intro W hW
        apply Submodule.eq_top_iff'.mpr
        intro y
        rcases Submodule.exists_mem_ne_zero_of_ne_bot (ne_of_gt hW) with
          ⟨w, hwW, hw_ne⟩
        have hyW : (y * w⁻¹) • w ∈ W := W.smul_mem (y * w⁻¹) hwW
        simpa [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hw_ne] using hyW
    have hkerCoatom : IsCoatom (LinearMap.ker f) := by
      exact (Submodule.isCoatom_comap_iff (f := f) hf_surj
        (p := (⊥ : Submodule (ZMod p) (ZMod p)))).2 hbotCoatom
    let Aker : AddSubgroup (Additive Q) :=
      (AddSubgroup.toZModSubmodule p).symm (LinearMap.ker f)
    let M : Subgroup Q := AddSubgroup.toSubgroup' Aker
    have hAkerCoatom : IsCoatom Aker :=
      ((AddSubgroup.toZModSubmodule p).symm.isCoatom_iff (LinearMap.ker f)).2
        hkerCoatom
    have hMCoatom : IsCoatom M :=
      (AddSubgroup.toSubgroup'.isCoatom_iff Aker).2 hAkerCoatom
    have hqM : q ∈ M := (frattini_le_coatom hMCoatom) hq
    have hvAker : v ∈ Aker := by
      simpa [M, v] using hqM
    have hvker : v ∈ LinearMap.ker f := by
      have hvsub : v ∈ (AddSubgroup.toZModSubmodule p) Aker := by
        simpa using hvAker
      simpa [Aker] using hvsub
    exact hfv_ne (by simpa [LinearMap.mem_ker] using hvker)
  have hPhi_eq_N : _root_.frattini G = N := by
    apply le_antisymm
    · have hle :=
        frattini_le_comap_frattini_of_surjective
          (φ := frattiniProjection p G) (frattiniProjection_surjective p G)
      rw [hPhiQ_bot] at hle
      have hle' : _root_.frattini G ≤ MonoidHom.ker (frattiniProjection p G) := by
        simpa only [MonoidHom.comap_bot] using hle
      rw [frattiniProjection_kernel] at hle'
      exact hle'
    · rw [_root_.frattini, Order.radical]
      refine le_iInf ?_
      intro M
      refine le_iInf ?_
      intro hM
      change mAKern p G ≤ M
      exact maximal_contains_abelianization
        (p := p) (G := G) hPG (M := M) hM
  have hCommEq : commutatorSubgroup G = _root_.commutator G := by
    rw [commutatorSubgroup, _root_.commutator_eq_closure]
    congr
    ext x
    simp [commutators, commutatorSet, commutatorElement_def, Set.mem_range]
  have hN_eq_join : N = pPowerSubgroup p G ⊔ commutatorSubgroup G := by
    calc
      N = Submission.modPFrattini p G := by
        simpa [N] using frattini_mod_p (p := p) (G := G)
      _ = pPowerSubgroup p G ⊔ _root_.commutator G := rfl
      _ = pPowerSubgroup p G ⊔ commutatorSubgroup G := by
        rw [hCommEq]
  exact hPhi_eq_N.trans hN_eq_join
/-- The second Zassenhaus term equals the Frattini subgroup. -/
theorem d2Phi {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) :
    GroupAlgebra.zSubgro p G 2 = Submission.Group.fSubgro p G
  := by
  classical
  have hp : Nat.Prime p := hG.1
  exact le_antisymm (zassenhaus_frattini (G := G) hp)
    (frattini_zassenhaus_two (G := G) hp)
/-- The second Zassenhaus term lies in the Frattini subgroup. -/
theorem dPhi {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) :
    GroupAlgebra.zSubgro p G 2 ≤ Submission.Group.fSubgro p G
  := by
  rw [d2Phi (p := p) (G := G) hG]
/-- Degree-two Zassenhaus/Frattini control. -/
theorem d2Control {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) :
    GroupAlgebra.zSubgro p G 2 = Submission.Group.fSubgro p G
  := by
  exact d2Phi (p := p) (G := G) hG
/-- The Frattini quotient is modeled by an elementary abelian F_p-vector space. -/
theorem frattiniElementaryAbelian {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) :
    FrattiniLinearModel (p := p) G
  := by
  letI : Fact p.Prime := fPGroups.fact_prime hG
  letI : Finite G := hG.finite
  let V : eFSpace.{u} p :=
    { fact_prime := fPGroups.fact_prime hG
      carrier := Submission.mFAdditi p G
      addCommGroup := (inferInstance : AddCommGroup (Submission.mFAdditi p G))
      module' := (inferInstance : Module (ZMod p) (Submission.mFAdditi p G))
      finite' := (inferInstance : Finite (Submission.mFAdditi p G))
      exponent_p := Submission.mod_additive_nsmul p G }
  refine ⟨V, ?_⟩
  dsimp [V]
  exact ⟨LinearEquiv.refl (ZMod p) (Submission.mFAdditi p G)⟩
/-- A degree-one basis spans the Frattini quotient. -/
theorem burnsideBasis {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) (S : Set G) :
    Subgroup.closure ((frattiniProjection p G) '' S) = ⊤ →
      Subgroup.closure S = ⊤
  := by
  classical
  intro hspan
  haveI : Fact (Nat.Prime p) := ⟨hG.1⟩
  haveI : Finite G := hG.2.1
  have hPG : IsPGroup p G := p_groups_group (p := p) (G := G) hG
  by_contra hnot
  let H : Subgroup G := Subgroup.closure S
  have hHne : H ≠ ⊤ := by
    simpa [H] using hnot
  obtain ⟨M, hHM, hMmax⟩ := maximal_subgroup (G := G) (H := H) hHne
  have hΦM : mAKern p G ≤ M :=
    maximal_contains_abelianization (p := p) hPG (G := G) (M := M) hMmax
  have himage_le :
      Subgroup.closure ((frattiniProjection p G) '' S) ≤
        Subgroup.map (frattiniProjection p G) M := by
    refine (Subgroup.closure_le (Subgroup.map (frattiniProjection p G) M)).2 ?_
    rintro q ⟨s, hsS, rfl⟩
    exact ⟨s, hHM (by simpa [H] using Subgroup.subset_closure hsS), rfl⟩
  have hmap_top : Subgroup.map (frattiniProjection p G) M = ⊤ := by
    apply eq_top_iff.mpr
    intro q hq
    exact himage_le (by simp [hspan])
  have hMtop : M = ⊤ := by
    apply eq_top_iff.mpr
    intro g hg
    have hgmap :
        frattiniProjection p G g ∈ Subgroup.map (frattiniProjection p G) M := by
      rw [hmap_top]
      trivial
    rcases hgmap with ⟨m, hmM, hm_eq⟩
    have hq : frattiniProjection p G (m⁻¹ * g) = 1 := by
      simp [map_mul, map_inv, hm_eq]
    have hq' :
        QuotientGroup.mk' (Submission.Group.fSubgro p G) (m⁻¹ * g) = 1 := by
      simpa [frattiniProjection, nSubgro.projection, quotientGroup,
        frattiniNormalSubgroup] using hq
    have hker : m⁻¹ * g ∈ Submission.Group.fSubgro p G :=
      (QuotientGroup.eq_one_iff (m⁻¹ * g)).mp hq'
    have hkerM : m⁻¹ * g ∈ M :=
      hΦM (by simpa [Submission.Group.fSubgro] using hker)
    have hprod : m * (m⁻¹ * g) ∈ M := M.mul_mem hmM hkerM
    simpa [mul_assoc] using hprod
  exact hMmax.1 hMtop
/-- A set generates a finite `p`-group iff its image generates the Frattini quotient. -/
theorem burnsideBasisEquivalence {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) (S : Set G) :
    generatingSet G S ↔
      generatingSet (frattiniQuotient p G) ((frattiniProjection p G) '' S)
  := by
  constructor
  · intro hS
    dsimp [generatingSet] at hS ⊢
    calc
      Subgroup.closure ((frattiniProjection p G) '' S)
          = Subgroup.map (frattiniProjection p G) (Subgroup.closure S) :=
            (MonoidHom.map_closure (frattiniProjection p G) S).symm
      _ = Subgroup.map (frattiniProjection p G) ⊤ := by rw [hS]
      _ = ⊤ :=
        Subgroup.map_top_of_surjective (frattiniProjection p G)
          (frattiniProjection_surjective p G)
  · intro hS
    exact burnsideBasis (p := p) (G := G) hG S (by
      simpa [generatingSet] using hS)

/-- The older least-generating-subset definition agrees with the clean
mod-`p` Frattini quotient rank. -/
theorem degree_generator_rank {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) :
    degreeGeneratorRank p G = Submission.generatorRank p G := by
  classical
  haveI : Fact p.Prime := ⟨hG.1⟩
  haveI : NeZero p := ⟨hG.1.ne_zero⟩
  have hker : Submission.Group.fSubgro p G = Submission.modPFrattini p G :=
    frattini_mod_p (p := p) (G := G)
  unfold degreeGeneratorRank Submission.generatorRank
  change
    sInf {c : Cardinal | ∃ S : Set (G ⧸ Submission.Group.fSubgro p G),
      Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c}
      = Module.rank (ZMod p) (Submission.mFAdditi p G)
  calc
    sInf {c : Cardinal | ∃ S : Set (G ⧸ Submission.Group.fSubgro p G),
      Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c}
        =
      sInf {c : Cardinal | ∃ S : Set (G ⧸ Submission.modPFrattini p G),
        Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c} :=
          multiplicative_inf_congr
            (QuotientGroup.quotientMulEquivOfEq hker)
    _ = Module.rank (ZMod p) (Submission.mFAdditi p G) := by
          simpa [Submission.mFAdditi, Submission.mFQuot] using
            (multiplicative_generator_rank (p := p)
              (A := Submission.mFQuot p G))

/-- Generator rank is the dimension of a linear model of the Frattini quotient. -/
theorem equalsFrattiniDimension {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) (V : eFSpace.{u} p)
    (hV : Nonempty (V.carrier ≃ₗ[ZMod p] Submission.mFAdditi p G)) :
    degreeGeneratorRank p G = Module.rank (ZMod p) V.carrier
  := by
  classical
  haveI : Fact p.Prime := ⟨hG.1⟩
  haveI : NeZero p := ⟨hG.1.ne_zero⟩
  have hker : Submission.Group.fSubgro p G = Submission.modPFrattini p G :=
    frattini_mod_p (p := p) (G := G)
  have hquot :
      degreeGeneratorRank p G =
        Module.rank (ZMod p) (Submission.mFAdditi p G) := by
    unfold degreeGeneratorRank
    change
      sInf {c : Cardinal | ∃ S : Set (G ⧸ Submission.Group.fSubgro p G),
        Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c}
        = Module.rank (ZMod p) (Submission.mFAdditi p G)
    calc
      sInf {c : Cardinal | ∃ S : Set (G ⧸ Submission.Group.fSubgro p G),
        Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c}
          =
        sInf {c : Cardinal | ∃ S : Set (G ⧸ Submission.modPFrattini p G),
          Subgroup.closure S = ⊤ ∧ Cardinal.mk S = c} :=
            multiplicative_inf_congr
              (QuotientGroup.quotientMulEquivOfEq hker)
      _ = Module.rank (ZMod p) (Submission.mFAdditi p G) := by
            simpa [Submission.mFAdditi, Submission.mFQuot] using
              (multiplicative_generator_rank (p := p)
                (A := Submission.mFQuot p G))
  obtain ⟨e⟩ := hV
  have hrank :
      Module.rank (ZMod p) V.carrier =
        Module.rank (ZMod p) (Submission.mFAdditi p G) := by
    simpa using (LinearEquiv.lift_rank_eq e)
  exact hquot.trans hrank.symm
/-- Generator rank is the size of the mod-p abelianization model. -/
theorem equalsAbelianizationDimension {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) (V : eFSpace.{u} p)
    (hV : Nonempty (V.carrier ≃ₗ[ZMod p] Submission.mFAdditi p G)) :
    degreeGeneratorRank p G = Module.rank (ZMod p) V.carrier
  := by
  exact equalsFrattiniDimension hG V hV

private lemma frattini_unchanged_aux {p : ℕ}
    {G : Type u} [Group G] (Q : fKQuot p G) :
    Nonempty (frattiniQuotient p (quotientGroup Q.kernel) ≃* frattiniQuotient p G)
  := by
  let ψ0 : G →* Submission.Group.frattiniQuotient p G :=
    QuotientGroup.mk' (Submission.Group.fSubgro p G)
  have hNker : Q.kernel.carrier ≤ ψ0.ker := by
    intro g hg
    change ψ0 g = 1
    dsimp [ψ0]
    exact (QuotientGroup.eq_one_iff (N := Submission.Group.fSubgro p G) g).mpr
      (Q.le_frattini hg)
  let ψ : Submission.Group.quotientGroup Q.kernel →* Submission.Group.frattiniQuotient p G :=
    QuotientGroup.lift Q.kernel.carrier ψ0 hNker
  have hψ :
      Submission.Group.fSubgro p (Submission.Group.quotientGroup Q.kernel) ≤ ψ.ker :=
    frattini_subgroup_ker
      (p := p) (A := Submission.Group.quotientGroup Q.kernel) (B := G) ψ
  let toG :
      Submission.Group.frattiniQuotient p (Submission.Group.quotientGroup Q.kernel) →*
        Submission.Group.frattiniQuotient p G :=
    QuotientGroup.lift
      (Submission.Group.fSubgro p (Submission.Group.quotientGroup Q.kernel)) ψ hψ
  let θ0 : G →* Submission.Group.frattiniQuotient p (Submission.Group.quotientGroup Q.kernel) :=
    (QuotientGroup.mk'
      (Submission.Group.fSubgro p (Submission.Group.quotientGroup Q.kernel))).comp
        (QuotientGroup.mk' Q.kernel.carrier)
  have hθ0 : Submission.Group.fSubgro p G ≤ θ0.ker :=
    frattini_subgroup_ker
      (p := p) (A := G) (B := Submission.Group.quotientGroup Q.kernel) θ0
  let toQ :
      Submission.Group.frattiniQuotient p G →*
        Submission.Group.frattiniQuotient p (Submission.Group.quotientGroup Q.kernel) :=
    QuotientGroup.lift (Submission.Group.fSubgro p G) θ0 hθ0
  refine ⟨
    { toFun := toG
      invFun := toQ
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }⟩
  · intro a
    refine Quotient.inductionOn a ?_
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    change toQ
        (toG ((QuotientGroup.mk' (Submission.Group.fSubgro p
          (Submission.Group.quotientGroup Q.kernel)))
          ((QuotientGroup.mk' Q.kernel.carrier) g))) =
      (QuotientGroup.mk' (Submission.Group.fSubgro p
        (Submission.Group.quotientGroup Q.kernel)))
        ((QuotientGroup.mk' Q.kernel.carrier) g)
    dsimp [toG, toQ, ψ, ψ0, θ0]
    rfl
  · intro b
    refine Quotient.inductionOn b ?_
    intro g
    change toG (toQ ((QuotientGroup.mk' (Submission.Group.fSubgro p G)) g)) =
      (QuotientGroup.mk' (Submission.Group.fSubgro p G)) g
    dsimp [toG, toQ, ψ, ψ0, θ0]
    rfl
  · intro x y
    exact toG.map_mul x y
/-- Quotienting by a Frattini-contained kernel preserves degree-one generator rank. -/
theorem quotientFrattiniSubgroup {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) :
    degreeGeneratorRank p (quotientGroup Q.kernel) = degreeGeneratorRank p G
  := by
  classical
  rcases frattini_unchanged_aux (p := p) (G := G) Q with ⟨e⟩
  unfold degreeGeneratorRank
  exact multiplicative_inf_congr e
/-- The Frattini quotient is unchanged by a Frattini-kernel quotient. -/
theorem frattiniUnchangedKernel {p : ℕ} {G : Type u} [Group G]
    (Q : fKQuot p G) :
    Nonempty (frattiniQuotient p (quotientGroup Q.kernel) ≃* frattiniQuotient p G)
  := by
  exact frattini_unchanged_aux (p := p) (G := G) Q
/-- A degree-one basis lifts to a minimal generating set. -/
theorem degreeLiftsGenerators {p : ℕ} {G : Type u} [Group G]
    (hG : fPGroups p G) (B : dOBasis p G) (lift : B.index → G)
    (hlift : ∀ i, frattiniProjection p G (lift i) = B.vector i) :
    minimalGeneratingSet G (Set.range lift) ∧
      (frattiniProjection p G) '' (Set.range lift) = Set.range B.vector
  := by
  classical
  haveI : Fact p.Prime := ⟨hG.1⟩
  haveI : NeZero p := ⟨hG.1.ne_zero⟩
  let eQ : frattiniQuotient p G ≃* Submission.mFQuot p G :=
    QuotientGroup.quotientMulEquivOfEq
      (frattini_mod_p (p := p) (G := G))
  let basisImage : Set (Submission.mFAdditi p G) :=
    Additive.ofMul '' (eQ '' Set.range B.vector)
  have hbasisClosure_modP :
      Subgroup.closure
          (eQ '' Set.range B.vector : Set (Submission.mFQuot p G)) = ⊤ :=
    closure_image_top eQ B.spans
  have hbasisImage_span :
      Submodule.span (ZMod p) basisImage = ⊤ := by
    simpa [basisImage] using
      (span_top_closure (p := p)
        (A := Submission.mFQuot p G)
        (S := (eQ '' Set.range B.vector : Set (Submission.mFQuot p G)))
        hbasisClosure_modP)
  have hbasisImage_linear : LinearIndepOn (ZMod p) id basisImage := by
    rw [linearIndepOn_iff_notMem_span]
    intro x hxBasis hxspan
    rcases hxBasis with ⟨q', ⟨q, hqBasis, rfl⟩, rfl⟩
    let T : Set (frattiniQuotient p G) := Set.range B.vector \ {q}
    have hxspan' :
        Additive.ofMul (eQ q) ∈
          Submodule.span (ZMod p)
            (basisImage \ {Additive.ofMul (eQ q)}) := by
      simpa using hxspan
    have hx_mem : Additive.ofMul (eQ q) ∈ basisImage := by
      exact ⟨eQ q, ⟨q, hqBasis, rfl⟩, rfl⟩
    have hbasis_eq_insert :
        basisImage = insert (Additive.ofMul (eQ q))
          (basisImage \ {Additive.ofMul (eQ q)}) := by
      ext y
      constructor
      · intro hy
        by_cases hyq : y = Additive.ofMul (eQ q)
        · exact Or.inl hyq
        · exact Or.inr ⟨hy, by simpa using hyq⟩
      · intro hy
        rcases hy with hy | hy
        · simpa [hy] using hx_mem
        · exact hy.1
    have hother_span :
        Submodule.span (ZMod p)
            (basisImage \ {Additive.ofMul (eQ q)}) = ⊤ := by
      rw [← Submodule.span_insert_eq_span hxspan']
      rw [← hbasis_eq_insert]
      exact hbasisImage_span
    have hother_eq :
        basisImage \ {Additive.ofMul (eQ q)} =
          Additive.ofMul '' (eQ '' T : Set (Submission.mFQuot p G)) := by
      ext y
      constructor
      · intro hy
        rcases hy.1 with ⟨q', ⟨q0, hq0, rfl⟩, rfl⟩
        refine ⟨eQ q0, ⟨q0, ⟨hq0, ?_⟩, rfl⟩, rfl⟩
        intro hq0q
        exact hy.2 (by simpa [hq0q])
      · rintro ⟨q', ⟨q0, hq0, rfl⟩, rfl⟩
        refine ⟨⟨eQ q0, ⟨q0, hq0.1, rfl⟩, rfl⟩, ?_⟩
        intro hmem
        have hq0q : q0 = q := by
          have hadd :
              Additive.ofMul (eQ q0) = Additive.ofMul (eQ q) := by
            simpa using hmem
          exact eQ.injective (Additive.ofMul.injective hadd)
        exact hq0.2 hq0q
    have hspan_T_add :
        Submodule.span (ZMod p)
            (Additive.ofMul '' (eQ '' T : Set (Submission.mFQuot p G))) =
          ⊤ := by
      simpa [hother_eq] using hother_span
    have hclosure_eT :
        Subgroup.closure (eQ '' T : Set (Submission.mFQuot p G)) = ⊤ :=
      closure_top_span (p := p)
        (A := Submission.mFQuot p G)
        (S := (eQ '' T : Set (Submission.mFQuot p G))) hspan_T_add
    have hclosure_T : Subgroup.closure T = ⊤ := by
      have h :=
        closure_image_top eQ.symm hclosure_eT
      have hpreimage : eQ.symm '' (eQ '' T : Set (Submission.mFQuot p G)) = T := by
        ext y
        constructor
        · rintro ⟨z, ⟨t, ht, rfl⟩, hy⟩
          have hty : t = y := by
            simpa using congrArg eQ hy
          simpa [← hty] using ht
        · intro hy
          exact ⟨eQ y, ⟨y, hy, rfl⟩, by simp⟩
      simpa [hpreimage] using h
    have hTproper : T ⊂ Set.range B.vector := by
      refine ⟨fun y hy => hy.1, ?_⟩
      intro hEq
      have hqT : q ∈ T := hEq hqBasis
      exact hqT.2 rfl
    exact (B.minimal T hTproper) hclosure_T
  have hcard_lift_basisImage :
      Cardinal.mk (Set.range lift) = Cardinal.mk basisImage := by
    let toBasisImage : Set.range lift → basisImage := fun x =>
      ⟨Additive.ofMul (eQ (frattiniProjection p G x.1)), by
        rcases x.2 with ⟨i, hi⟩
        exact ⟨eQ (B.vector i), ⟨B.vector i, ⟨i, rfl⟩, rfl⟩, by
          simp [← hi, hlift i]⟩⟩
    exact Cardinal.mk_congr (Equiv.ofBijective toBasisImage (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        rcases x.2 with ⟨i, hi⟩
        rcases y.2 with ⟨j, hj⟩
        have hproj :
            frattiniProjection p G x.1 =
              frattiniProjection p G y.1 := by
          have hadd :
              Additive.ofMul (eQ (frattiniProjection p G x.1)) =
                Additive.ofMul (eQ (frattiniProjection p G y.1)) :=
            Subtype.ext_iff.mp hxy
          exact eQ.injective (Additive.ofMul.injective hadd)
        have hvec : B.vector i = B.vector j := by
          rw [← hlift i, ← hlift j]
          simpa [hi, hj] using hproj
        have hij : i = j := B.injective hvec
        exact hi.symm.trans ((congrArg lift hij).trans hj)
      · intro y
        rcases y with ⟨m, hm⟩
        rcases hm with ⟨q', ⟨q, ⟨i, rfl⟩, rfl⟩, rfl⟩
        refine ⟨⟨lift i, ⟨i, rfl⟩⟩, ?_⟩
        apply Subtype.ext
        simp [toBasisImage, hlift i]))
  have himage :
      (frattiniProjection p G) '' (Set.range lift) = Set.range B.vector := by
    ext q
    constructor
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hlift i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨lift i, ⟨i, rfl⟩, hlift i⟩
  have hgen : generatingSet G (Set.range lift) := by
    exact burnsideBasis (p := p) (G := G) hG (Set.range lift) (by
      simpa [himage] using B.spans)
  have hminimal :
      ∀ T : Set G, generatingSet G T →
        Cardinal.mk (Set.range lift) ≤ Cardinal.mk T := by
    intro T hTgen
    let W : Set (Submission.mFAdditi p G) :=
      Set.range fun t : T => Additive.ofMul (eQ (frattiniProjection p G t.1))
    have hTimage_span :
        Subgroup.closure ((frattiniProjection p G) '' T) = ⊤ := by
      calc
        Subgroup.closure ((frattiniProjection p G) '' T)
            = Subgroup.map (frattiniProjection p G) (Subgroup.closure T) :=
              (MonoidHom.map_closure (frattiniProjection p G) T).symm
        _ = Subgroup.map (frattiniProjection p G) ⊤ := by rw [hTgen]
        _ = ⊤ :=
          Subgroup.map_top_of_surjective (frattiniProjection p G)
            (frattiniProjection_surjective p G)
    have hW_span : Submodule.span (ZMod p) W = ⊤ := by
      let imageSet : Set (Submission.mFQuot p G) :=
        eQ '' ((frattiniProjection p G) '' T)
      have hclosure_imageSet : Subgroup.closure imageSet = ⊤ := by
        exact closure_image_top eQ hTimage_span
      have hW_eq : W = Additive.ofMul '' imageSet := by
        ext x
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨eQ (frattiniProjection p G t.1),
            ⟨frattiniProjection p G t.1, ⟨t.1, t.2, rfl⟩, rfl⟩, rfl⟩
        · rintro ⟨q', ⟨q, ⟨g, hgT, rfl⟩, rfl⟩, rfl⟩
          exact ⟨⟨g, hgT⟩, rfl⟩
      simpa [W, imageSet, hW_eq] using
        (span_top_closure (p := p)
          (A := Submission.mFQuot p G) (S := imageSet)
          hclosure_imageSet)
    have hlinSubtype :
        LinearIndependent (ZMod p)
          ((↑) : basisImage → Submission.mFAdditi p G) := by
      simpa [LinearIndepOn] using hbasisImage_linear
    have hbasis_le_W : Cardinal.mk basisImage ≤ Cardinal.mk W :=
      linearIndependent_le_span'' hlinSubtype W hW_span
    have hW_le_T : Cardinal.mk W ≤ Cardinal.mk T := by
      simpa [W] using
        (Cardinal.mk_range_le
          (f := fun t : T => Additive.ofMul (eQ (frattiniProjection p G t.1))))
    calc
      Cardinal.mk (Set.range lift) = Cardinal.mk basisImage := hcard_lift_basisImage
      _ ≤ Cardinal.mk W := hbasis_le_W
      _ ≤ Cardinal.mk T := hW_le_T
  exact ⟨⟨hgen, hminimal⟩, himage⟩
/-- Minimal p-presentation relators have depth at least two once depth is tied to
vanishing of the degree-one linear part. -/
theorem minimalHaveLeast {p : ℕ}
    (M : mPPres.{u} p) (depths : M.pres.rels → ℕ)
    (linearPart : M.pres.rels → M.pres.Gen → ZMod p)
    (hminimal_linear : ∀ r a, linearPart r a = 0)
    (hdepth_detects_linear : ∀ r, (∀ a, linearPart r a = 0) → 2 ≤ depths r) :
    ∀ r : M.pres.rels, 2 ≤ depths r
  := by
  intro r
  exact hdepth_detects_linear r (fun a => hminimal_linear r a)
/-- Relators in minimal p-presentations are killed and have positive depth. -/
theorem relatorsMinimalPresentation
    (P : presentations.{u}) (depths : P.rels → ℕ)
    (hdepth : ∀ r, 0 < depths r) (r : P.rels) :
    P.quotientMap r.1 = 1 ∧ 0 < depths r
  := by
  exact ⟨P.quotient_rel_one r.2, hdepth r⟩

end Theorems
end Submission
