import Submission.Group.HallWords
import Submission.Group.ProPTopology
import Submission.Group.DenseGenerators.ZassenhausSurjective
import Submission.Group.DenseGenerators.ZassenhausDegreeTwo
import Submission.Group.HallRecursiveCollection
import Submission.Group.HallPetresco
import Submission.Group.Zassenhaus.HallPetrescoBoundary
import Submission.Group.ZassenhausRestricted

/-!
# Finite p-group collection schemes for Zassenhaus terms

This file isolates the finite algebra input needed to prove closedness of
Zassenhaus terms in finitely generated pro-`p` groups.  A scheme is a
commutator word followed by a prime-power operation.  Its level bound ensures
that every value is a raw Zassenhaus generator.

The remaining finite-group collection theorem is intentionally stated without
topology.  Its proof is the collection argument: repeatedly insert one raw
factor into a collected normal form and move correction factors to strictly
higher weight.
-/

open scoped Topology commutatorElement

noncomputable section

namespace Submission

universe u v

/-- A commutator word followed by a `p`-power operation whose weight is at
least the requested Zassenhaus level. -/
structure ZWScheme (p n : ℕ) where
  arity : ℕ
  word : CWord (Fin arity)
  frobenius : ℕ
  level_bound :
    n ≤ word.weight (fun _ => 1) * p ^ frobenius

namespace ZWScheme

/-- The lower-central index represented by a scheme, in the zero-based
convention used by `lowerCentralSeries`. -/
def lowerLevel
    {p n : ℕ}
    (S : ZWScheme p n) :
    ℕ :=
  S.word.weight (fun _ => 1) - 1

/-- A scheme word has positive lower-central weight because each atom has
weight one. -/
lemma word_weight_pos
    {p n : ℕ}
    (S : ZWScheme p n) :
    0 < S.word.weight (fun _ => 1) := by
  exact
    CWord.weight_pos
      (wt := fun _ : Fin S.arity => 1)
      (fun _ => by simp)
      S.word

/-- Converting the positive one-based word weight to the zero-based
lower-central index and back loses no information. -/
lemma lower_level_add
    {p n : ℕ}
    (S : ZWScheme p n) :
    S.lowerLevel + 1 = S.word.weight (fun _ => 1) := by
  dsimp [lowerLevel]
  exact
    Nat.sub_add_cancel
      (show 1 ≤ S.word.weight (fun _ => 1) from S.word_weight_pos)

/-- Evaluate the powered commutator word represented by a scheme. -/
def eval
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G]
    (a : Fin S.arity → G) :
    G :=
  S.word.eval a ^ (p ^ S.frobenius)

lemma eval_def
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G]
    (a : Fin S.arity → G) :
    S.eval a = S.word.eval a ^ (p ^ S.frobenius) := by
  rfl

/-- Scheme evaluation commutes with group homomorphisms. -/
lemma eval_map
    {p n : ℕ}
    (S : ZWScheme p n)
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (a : Fin S.arity → G) :
    φ (S.eval a) = S.eval (fun i => φ (a i)) := by
  rw [eval_def, map_pow, eval_def]
  exact congrArg (fun x : H => x ^ (p ^ S.frobenius))
    (CWord.map_eval φ a S.word)

/-- A commutator word is continuous when its atomic inputs vary
continuously. -/
lemma continuous_word_eval
    {α X G : Type*}
    [TopologicalSpace X]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : α → X → G)
    (hf : ∀ i, Continuous (f i)) :
    ∀ w : CWord α,
      Continuous (fun x => w.eval (fun i => f i x))
  | CWord.atom i => by
      simpa using hf i
  | CWord.commutator left right => by
      simp only [CWord.eval_commutator, commutatorElement_def]
      exact
        (((continuous_word_eval f hf left).mul
          (continuous_word_eval f hf right)).mul
            (continuous_word_eval f hf left).inv).mul
              (continuous_word_eval f hf right).inv

/-- A scheme is a continuous word map on every topological group. -/
lemma continuous_eval
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Continuous (fun a : Fin S.arity → G => S.eval a) := by
  exact
    (continuous_word_eval
      (fun i : Fin S.arity => fun a : Fin S.arity → G => a i)
      (fun i => continuous_apply i)
      S.word).pow _

/-- Evaluating the unpowered commutator word lands in the lower-central term
prescribed by the scheme weight. -/
lemma word_lower_series
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G]
    (a : Fin S.arity → G) :
    S.word.eval a ∈ Subgroup.lowerCentralSeries G S.lowerLevel := by
  have hatom :
      ∀ i : Fin S.arity,
        a i ∈ Subgroup.lowerCentralSeries G ((fun _ : Fin S.arity => 1) i - 1) := by
    intro i
    simp [Subgroup.lowerCentralSeries_zero]
  simpa [lowerLevel] using
    (CWord.eval_lower_series
      a
      (fun _ : Fin S.arity => 1)
      (fun _ => by simp)
      hatom
      S.word)

/-- Every scheme value is one of the raw generators used to define the
Zassenhaus term. -/
lemma eval_generator_set
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G]
    (a : Fin S.arity → G) :
    S.eval a ∈ zassenhausGeneratorSet p G n := by
  refine
    ⟨S.lowerLevel, S.frobenius, S.word.eval a, ?_, ?_, ?_⟩
  · exact S.word_lower_series a
  · rw [S.lower_level_add]
    exact S.level_bound
  · rfl

/-- Every scheme value lies in the corresponding explicit Zassenhaus
subgroup. -/
lemma eval_zassenhaus_filtration
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G]
    (a : Fin S.arity → G) :
    S.eval a ∈ zassenhausFiltration p G n := by
  exact
    Subgroup.subset_closure
      (S.eval_generator_set a)

/-- The range of a scheme in a chosen group. -/
def range
    {p n : ℕ}
    (S : ZWScheme p n)
    (G : Type u) [Group G] :
    Set G :=
  Set.range fun a : Fin S.arity → G => S.eval a

lemma mem_range_iff
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G]
    {x : G} :
    x ∈ S.range G ↔
      ∃ a : Fin S.arity → G, S.eval a = x := by
  rfl

/-- Scheme ranges consist of raw generators at the requested level. -/
lemma range_subset_set
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G] :
    S.range G ⊆ zassenhausGeneratorSet p G n := by
  intro x hx
  rcases hx with ⟨a, rfl⟩
  exact S.eval_generator_set a

/-- Scheme ranges are compact in compact topological groups. -/
lemma range_isCompact
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] :
    IsCompact (S.range G) := by
  haveI : CompactSpace (Fin S.arity → G) := inferInstance
  simpa [range] using
    (@isCompact_range
      (Fin S.arity → G)
      G
      _
      _
      inferInstance
      (fun a : Fin S.arity → G => S.eval a)
      S.continuous_eval)

/-- Package a scheme as the generic compact-cover word map used by the
dense-generator topology layer. -/
def generatorWord
    {p n : ℕ}
    (S : ZWScheme p n)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    WGWord p G n where
  arity := S.arity
  map := fun a => S.eval a
  map_continuous := S.continuous_eval
  map_generators := by
    intro a
    exact S.eval_generator_set a

lemma generator_word
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (a : Fin S.arity → G) :
    (S.generatorWord G).map a = S.eval a := by
  rfl

lemma generator_word_range
    {p n : ℕ}
    (S : ZWScheme p n)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Set.range (S.generatorWord G).map = S.range G := by
  rfl

end ZWScheme

/-- A quotient-independent finite list of powered commutator schemes. -/
structure ZWSched (p d n : ℕ) where
  width : ℕ
  slot : Fin width → ZWScheme p n

namespace ZWSched

/-- Arguments for every slot in a schedule. -/
abbrev Arguments
    {p d n : ℕ}
    (S : ZWSched p d n)
    (G : Type u) :=
  ∀ i : Fin S.width, Fin (S.slot i).arity → G

/-- Evaluate every slot in schedule order. -/
def values
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G]
    (a : S.Arguments G) :
    Fin S.width → G :=
  fun i => (S.slot i).eval (a i)

/-- Multiply the slot values in schedule order. -/
def eval
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G]
    (a : S.Arguments G) :
    G :=
  (List.ofFn (S.values a)).prod

lemma eval_def
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G]
    (a : S.Arguments G) :
    S.eval a =
      (List.ofFn fun i : Fin S.width => (S.slot i).eval (a i)).prod := by
  rfl

/-- A schedule is a continuous finite product of continuous word maps. -/
lemma continuous_eval
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Continuous (fun a : S.Arguments G => S.eval a) := by
  change
    Continuous
      (fun a : S.Arguments G =>
        (List.ofFn fun i : Fin S.width => (S.slot i).eval (a i)).prod)
  simpa [List.map_ofFn] using
    (continuous_list_prod
      (List.ofFn fun i : Fin S.width => i)
      (fun i _ =>
        (S.slot i).continuous_eval.comp (continuous_apply i)))

/-- Evaluating an entire schedule commutes with group homomorphisms. -/
lemma eval_map
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G H : Type u} [Group G] [Group H]
    (φ : G →* H)
    (a : S.Arguments G) :
    φ (S.eval a) =
      S.eval (fun i j => φ (a i j)) := by
  rw [eval_def, eval_def, map_list_prod]
  rw [List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact (S.slot i).eval_map φ (a i)

/-- View all scheme ranges in a schedule as a finite family of sets. -/
def ranges
    {p d n : ℕ}
    (S : ZWSched p d n)
    (G : Type u) [Group G] :
    Fin S.width → Set G :=
  fun i => (S.slot i).range G

/-- Each scheduled range consists of raw Zassenhaus generators. -/
lemma ranges_subset_set
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G] :
    ∀ i : Fin S.width,
      S.ranges G i ⊆ zassenhausGeneratorSet p G n := by
  intro i
  exact (S.slot i).range_subset_set

/-- Each scheduled range is compact in a compact topological group. -/
lemma ranges_isCompact
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] :
    ∀ i : Fin S.width, IsCompact (S.ranges G i) := by
  intro i
  exact (S.slot i).range_isCompact

/-- Turn a schedule into the word-map family expected by the existing compact
cover infrastructure. -/
def generatorWordFamily
    {p d n : ℕ}
    (S : ZWSched p d n)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Fin S.width → WGWord p G n :=
  fun i => (S.slot i).generatorWord G

lemma generator_family_range
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (i : Fin S.width) :
    Set.range ((S.generatorWordFamily G i).map) = S.ranges G i := by
  rfl

/-- A concrete schedule evaluation belongs to the finite product of its
ranges. -/
lemma eval_product_image
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G]
    (a : S.Arguments G) :
    S.eval a ∈ zassenhausProductImage (S.ranges G) := by
  refine ⟨fun i => ⟨(S.slot i).eval (a i), ?_⟩, ?_⟩
  · exact ⟨a i, rfl⟩
  · rfl

/-- The finite product represented by a schedule stays inside the target
Zassenhaus subgroup. -/
lemma subset_zassenhaus_filtration
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type u} [Group G] :
    zassenhausProductImage (S.ranges G) ⊆
      ((zassenhausFiltration p G n : Subgroup G) : Set G) := by
  exact
    image_subset_filtration
      (S.ranges_subset_set)

end ZWSched

/-- A uniform collection schedule for the `n`th Zassenhaus term in finite
`d`-generated `p`-groups.  This is a finite-algebra statement: it has no
topological hypotheses and no closedness conclusion. -/
structure FSColl (p d n : ℕ) where
  schedule : ZWSched p d n
  factor :
    ∀ (Q : Type u) [Group Q] [Finite Q],
      IsPGroup p Q →
      ∀ t : Fin d → Q,
        GeneratedBy t →
        ∀ x : Q,
          x ∈ zassenhausFiltration p Q n →
            ∃ a : schedule.Arguments Q,
              schedule.eval a = x

namespace FSColl

/-- The collection theorem immediately places every finite quotient term in
the product of the scheduled ranges. -/
lemma mem_product
    {p d n : ℕ}
    (C : FSColl.{u} p d n)
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q)
    (t : Fin d → Q)
    (ht : GeneratedBy t)
    {x : Q}
    (hx : x ∈ zassenhausFiltration p Q n) :
    x ∈ zassenhausProductImage (C.schedule.ranges Q) := by
  rcases C.factor Q hQ t ht x hx with ⟨a, rfl⟩
  exact C.schedule.eval_product_image a

/-- Pointwise factorization form of the finite collection theorem. -/
lemma exists_factorization
    {p d n : ℕ}
    (C : FSColl.{u} p d n)
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q)
    (t : Fin d → Q)
    (ht : GeneratedBy t)
    {x : Q}
    (hx : x ∈ zassenhausFiltration p Q n) :
    ∃ f : Fin C.schedule.width → Q,
      (∀ i, f i ∈ (C.schedule.slot i).range Q) ∧
        (List.ofFn f).prod = x := by
  rcases C.factor Q hQ t ht x hx with ⟨a, hprod⟩
  refine ⟨fun i => (C.schedule.slot i).eval (a i), ?_, ?_⟩
  · intro i
    exact ⟨a i, rfl⟩
  · simpa [ZWSched.eval_def] using hprod

end FSColl

/-- A finite family of admissible schemes together with a quotient-independent
product-length bound.  Each factor position may choose any member of the
family, so no fixed ordering of word maps is imposed. -/
structure PGColl (p d n : ℕ) where
  family : ZWSched p d n
  bound : ℕ
  factor :
    ∀ (Q : Type u) [Group Q] [Finite Q],
      IsPGroup p Q →
      ∀ t : Fin d → Q,
        GeneratedBy t →
        ∀ x : Q,
          x ∈ zassenhausFiltration p Q n →
            x ∈ zassenhausProductImage
              (fun _ : Fin bound =>
                zassenhausUnionImage (family.ranges Q))

namespace PGColl

/-- The repeated compact piece associated to a uniformly bounded family. -/
def pieces
    {p d n : ℕ}
    (C : PGColl.{u} p d n)
    (G : Type u) [Group G] :
    Fin C.bound → Set G :=
  fun _ => zassenhausUnionImage (C.family.ranges G)

/-- Every repeated family piece consists of raw Zassenhaus generators. -/
lemma pieces_subset_set
    {p d n : ℕ}
    (C : PGColl.{u} p d n)
    {G : Type u} [Group G] :
    ∀ i : Fin C.bound,
      C.pieces G i ⊆ zassenhausGeneratorSet p G n := by
  intro i
  exact
    union_subset_set
      C.family.ranges_subset_set

/-- Every repeated family piece is compact in a compact topological group. -/
lemma pieces_isCompact
    {p d n : ℕ}
    (C : PGColl.{u} p d n)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] :
    ∀ i : Fin C.bound, IsCompact (C.pieces G i) := by
  intro i
  exact union_image_compact C.family.ranges_isCompact

end PGColl

/-- Forget the fixed slot order in a collection schedule, retaining only its
finite family of schemes and uniform width. -/
def FSColl.toCollection
    {p d n : ℕ}
    (C : FSColl.{u} p d n) :
    PGColl.{u} p d n where
  family := C.schedule
  bound := C.schedule.width
  factor := by
    intro Q _ _ hQ t ht x hx
    rcases C.mem_product hQ t ht hx with ⟨f, hprod⟩
    refine ⟨fun i => ⟨f i, ?_⟩, hprod⟩
    exact
      (zassenhaus_union_image
        (K := C.schedule.ranges Q)).mpr
        ⟨i, (f i).property⟩

/-- At levels zero and one, one atom is already an admissible scheme. -/
def zassenhausSchemeOne
    (p n : ℕ)
    (hn : n ≤ 1) :
    ZWScheme p n where
  arity := 1
  word := .atom 0
  frobenius := 0
  level_bound := by
    simpa using hn

/-- The single atomic slot used for the low-level collection theorem. -/
def zassenhausScheduleOne
    (p d n : ℕ)
    (hn : n ≤ 1) :
    ZWSched p d n where
  width := 1
  slot := fun _ => zassenhausSchemeOne p n hn

/-- The finite p-group collection statement is immediate at levels zero and
one: the requested element itself can be supplied as the atomic argument. -/
theorem p_collection_one
    (p d n : ℕ) [Fact p.Prime]
    (hn : n ≤ 1) :
    Nonempty (FSColl.{u} p d n) := by
  refine ⟨{
    schedule := zassenhausScheduleOne p d n hn
    factor := ?_ }⟩
  intro Q _ _ _ _ _ x _
  refine ⟨fun _ _ => x, ?_⟩
  simp [ZWSched.eval, ZWSched.values,
    ZWScheme.eval, zassenhausScheduleOne,
    zassenhausSchemeOne]

/-- With no generators, the empty schedule suffices. -/
def zassenhausScheduleZero
    (p n : ℕ) :
    ZWSched p 0 n where
  width := 0
  slot := Fin.elim0

/-- A group generated by the empty tuple is trivial, so its Zassenhaus terms
are represented by the empty product at every level. -/
theorem collection_zero_generators
    (p n : ℕ) [Fact p.Prime] :
    Nonempty (FSColl.{u} p 0 n) := by
  refine ⟨{
    schedule := zassenhausScheduleZero p n
    factor := ?_ }⟩
  intro Q _ _ _ _ ht x _
  have hbot : (⊥ : Subgroup Q) = ⊤ := by
    simpa [GeneratedBy] using ht
  have hx : x = 1 := by
    have hxbot : x ∈ (⊥ : Subgroup Q) := by
      rw [hbot]
      exact trivial
    simpa using hxbot
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  simp [ZWSched.eval, zassenhausScheduleZero, hx]

/-- Large enough prime powers exist, using only primality. -/
lemma tmp_prime_pow
    (p n : ℕ) [Fact p.Prime] :
    ∃ j : ℕ, n ≤ p ^ j := by
  refine ⟨n, ?_⟩
  exact
    n.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_left ((Fact.out : Nat.Prime p).two_le) n)

/-- The least exponent whose `p`-power reaches the requested level. -/
noncomputable def leastPrimeExponent
    (p n : ℕ) [Fact p.Prime] :
    ℕ :=
  Nat.find (tmp_prime_pow p n)

lemma pow_least_exponent
    (p n : ℕ) [Fact p.Prime] :
    n ≤ p ^ leastPrimeExponent p n := by
  exact Nat.find_spec (tmp_prime_pow p n)

lemma least_power_exponent
    {p n j : ℕ} [Fact p.Prime]
    (h : n ≤ p ^ j) :
    leastPrimeExponent p n ≤ j := by
  exact Nat.find_min' (tmp_prime_pow p n) h

/-- One atomic prime-power slot is enough in the cyclic case. -/
def zassenhausSchemeGenerator
    (p n : ℕ) [Fact p.Prime] :
    ZWScheme p n where
  arity := 1
  word := .atom 0
  frobenius := leastPrimeExponent p n
  level_bound := by
    simpa using pow_least_exponent p n

/-- The one-slot schedule used for cyclic finite p-groups. -/
def zassenhausScheduleGenerator
    (p n : ℕ) [Fact p.Prime] :
    ZWSched p 1 n where
  width := 1
  slot := fun _ => zassenhausSchemeGenerator p n

/-- In a commutative group, every `D_n` element is a `p^e`th power for the
least exponent `e` such that `n ≤ p^e`. -/
lemma zassenhaus_filtration_comm
    (p n : ℕ) [Fact p.Prime]
    (Q : Type u) [CommGroup Q] :
    zassenhausFiltration p Q n ≤
      powerSubgroup Q (p ^ leastPrimeExponent p n) := by
  rw [zassenhausFiltration]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨i, j, x, hx, hlevel, rfl⟩
  by_cases hi : i = 0
  · subst i
    have hn_pow : n ≤ p ^ j := by
      simpa using hlevel
    have he_le_j : leastPrimeExponent p n ≤ j :=
      least_power_exponent hn_pow
    rcases Nat.exists_eq_add_of_le he_le_j with ⟨k, rfl⟩
    have hpow :
        x ^ (p ^ (leastPrimeExponent p n + k)) =
          (x ^ (p ^ k)) ^ (p ^ leastPrimeExponent p n) := by
      calc
        x ^ (p ^ (leastPrimeExponent p n + k)) =
            x ^ (p ^ leastPrimeExponent p n * p ^ k) := by
              rw [pow_add]
        _ = x ^ (p ^ k * p ^ leastPrimeExponent p n) := by
              rw [Nat.mul_comm]
        _ = (x ^ (p ^ k)) ^ (p ^ leastPrimeExponent p n) := by
              rw [pow_mul]
    rw [hpow]
    exact pow_power_subgroup _ _
  · have hi_pos : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
    have hx_comm : x ∈ commutator Q :=
      lower_series_commutator hi_pos hx
    have hcomm : commutator Q = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      exact CommGroup.center_eq_top
    have hx_one : x = 1 := by
      have : x ∈ (⊥ : Subgroup Q) := by
        rwa [← hcomm]
      simpa using this
    rw [hx_one, one_pow]
    exact (powerSubgroup Q (p ^ leastPrimeExponent p n)).one_mem

/-- A group generated by one element is cyclic. -/
lemma tmp_cyclic_generated
    {G : Type u} [Group G] {t : Fin 1 → G}
    (ht : GeneratedBy t) :
    IsCyclic G := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨t 0, ?_⟩
  rw [Subgroup.zpowers_eq_closure]
  have hrange : Set.range t = ({t 0} : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      simp
    · intro hx
      rcases hx with rfl
      exact ⟨0, rfl⟩
  simpa [GeneratedBy, hrange] using ht

/-- In a commutative group, the normal closure of the `m`th powers is the
range of the `m`th-power homomorphism. -/
lemma tmp_monoid_comm
    (G : Type u) [CommGroup G] (m : ℕ) :
    powerSubgroup G m = (powMonoidHom (α := G) m).range := by
  apply le_antisymm
  · dsimp [powerSubgroup]
    exact
      Subgroup.normalClosure_le_normal (by
        rintro y ⟨x, rfl⟩
        exact ⟨x, rfl⟩)
  · rintro y ⟨x, rfl⟩
    exact pow_power_subgroup m x

/-- The collection theorem holds for one-generated finite p-groups at every
level: cyclicity reduces `D_n` to one prime-power word map. -/
theorem p_collection_generator
    (p n : ℕ) [Fact p.Prime] :
    Nonempty (FSColl.{u} p 1 n) := by
  refine ⟨{
    schedule := zassenhausScheduleGenerator p n
    factor := ?_ }⟩
  intro Q _ _ _ t ht x hx
  have hcyc : IsCyclic Q :=
    tmp_cyclic_generated (G := Q) (t := t) ht
  letI : CommGroup Q := IsCyclic.commGroup
  have hx_power :
      x ∈ powerSubgroup Q (p ^ leastPrimeExponent p n) :=
    zassenhaus_filtration_comm p n Q hx
  have hx_range :
      x ∈ (powMonoidHom (α := Q) (p ^ leastPrimeExponent p n)).range := by
    simpa [tmp_monoid_comm Q
      (p ^ leastPrimeExponent p n)] using hx_power
  rcases hx_range with ⟨y, hy⟩
  refine ⟨fun _ _ => y, ?_⟩
  simpa [ZWSched.eval, ZWSched.values,
    ZWScheme.eval, zassenhausScheduleGenerator,
    zassenhausSchemeGenerator] using hy

/-- The elementary construction covers all generator counts at most one. -/
theorem p_collection_generators
    {p d n : ℕ} [Fact p.Prime]
    (hd : d ≤ 1) :
    Nonempty (FSColl.{u} p d n) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with rfl | rfl
  · exact collection_zero_generators p n
  · exact p_collection_generator p n

namespace ZWScheme

/-- Transport an argument tuple across an equality of schemes. -/
def castArguments
    {p n : ℕ}
    {S T : ZWScheme p n}
    {G : Type*}
    (h : S = T)
    (a : Fin S.arity → G) :
    Fin T.arity → G :=
  cast (congrArg (fun U : ZWScheme p n => Fin U.arity → G) h) a

@[simp]
lemma eval_castArguments
    {p n : ℕ}
    {S T : ZWScheme p n}
    {G : Type*} [Group G]
    (h : S = T)
    (a : Fin S.arity → G) :
    T.eval (castArguments h a) = S.eval a := by
  subst T
  rfl

end ZWScheme

namespace ZWSched

/-- Concatenation of schedules. -/
def append
    {p d n : ℕ}
    (S T : ZWSched p d n) :
    ZWSched p d n where
  width := S.width + T.width
  slot := Fin.addCases S.slot T.slot

@[simp]
lemma append_slot_cast
    {p d n : ℕ}
    (S T : ZWSched p d n)
    (j : Fin S.width) :
    (S.append T).slot (Fin.castAdd T.width j) = S.slot j := by
  simp [append]

@[simp]
lemma append_slot_add
    {p d n : ℕ}
    (S T : ZWSched p d n)
    (j : Fin T.width) :
    (S.append T).slot (Fin.natAdd S.width j) = T.slot j := by
  simp [append]

/-- Concatenation of argument tuples for concatenated schedules. -/
def appendArguments
    {p d n : ℕ}
    (S T : ZWSched p d n)
    {G : Type*}
    (a : S.Arguments G)
    (b : T.Arguments G) :
    (S.append T).Arguments G :=
  Fin.addCases
    (fun j =>
      ZWScheme.castArguments (append_slot_cast S T j).symm (a j))
    (fun j =>
      ZWScheme.castArguments (append_slot_add S T j).symm (b j))

@[simp]
lemma eval_append
    {p d n : ℕ}
    (S T : ZWSched p d n)
    {G : Type*} [Group G]
    (a : S.Arguments G)
    (b : T.Arguments G) :
    (S.append T).eval (S.appendArguments T a b) = S.eval a * T.eval b := by
  have hvalues :
      (S.append T).values (S.appendArguments T a b) =
        Fin.append (S.values a) (T.values b) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [Fin.append_left]
      unfold values
      rw [appendArguments, Fin.addCases_left]
      exact ZWScheme.eval_castArguments _ _
    · intro j
      rw [Fin.append_right]
      unfold values
      rw [appendArguments, Fin.addCases_right]
      exact ZWScheme.eval_castArguments _ _
  rw [eval, hvalues, eval, eval]
  calc
    (List.ofFn (Fin.append (S.values a) (T.values b))).prod =
        (List.ofFn (S.values a) ++ List.ofFn (T.values b)).prod := by
          rw [List.ofFn_fin_append]
    _ = (List.ofFn (S.values a)).prod * (List.ofFn (T.values b)).prod := by
      rw [List.prod_append]

/-- Fill every argument of a schedule with the identity element. -/
def oneArguments
    {p d n : ℕ}
    (S : ZWSched p d n)
    (G : Type*) [One G] :
    S.Arguments G :=
  fun _ _ => 1

@[simp]
lemma CWord.eval_one
    {α G : Type*} [Group G]
    (w : CWord α) :
    w.eval (fun _ => (1 : G)) = 1 := by
  induction w with
  | atom _ => rfl
  | commutator left right hleft hright =>
      simp [CWord.eval, hleft, hright]

@[simp]
lemma eval_oneArguments
    {p d n : ℕ}
    (S : ZWSched p d n)
    (G : Type*) [Group G] :
    S.eval (S.oneArguments G) = 1 := by
  have hvalues : S.values (S.oneArguments G) = fun _ => 1 := by
    funext i
    change (S.slot i).eval (fun _ => (1 : G)) = 1
    simp [ZWScheme.eval]
  rw [eval, hvalues]
  simp

/-- Fill one selected schedule slot and put identity arguments in every other
slot. -/
def singleArguments
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type*} [One G]
    (z : Σ i : Fin S.width, Fin (S.slot i).arity → G) :
    S.Arguments G :=
  fun j =>
    if h : j = z.1 then
      ZWScheme.castArguments (congrArg S.slot h.symm) z.2
    else
      fun _ => 1

/-- A one-hot argument tuple evaluates to its selected slot value. -/
lemma eval_singleArguments
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type*} [Group G]
    (z : Σ i : Fin S.width, Fin (S.slot i).arity → G) :
    S.eval (S.singleArguments z) = (S.slot z.1).eval z.2 := by
  rw [eval_def, List.ofFn_eq_map]
  rw [List.prod_map_eq_pow_single z.1]
  · simp [singleArguments, List.count_finRange]
  · intro j hj _hjmem
    simp [singleArguments, hj, ZWScheme.eval]

/-- Repeat a fixed schedule a prescribed number of times. -/
def repeatSchedule
    {p d n : ℕ}
    (S : ZWSched p d n) :
    ℕ → ZWSched p d n
  | 0 =>
      { width := 0
        slot := Fin.elim0 }
  | k + 1 => S.append (repeatSchedule S k)

/-- Concatenate one argument tuple for each repeated block. -/
def repeatArguments
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type*} :
    ∀ (k : ℕ), (Fin k → S.Arguments G) → (S.repeatSchedule k).Arguments G
  | 0, _ => fun i => Fin.elim0 i
  | k + 1, a =>
      S.appendArguments (S.repeatSchedule k)
        (a 0)
        (S.repeatArguments k fun i => a i.succ)

/-- Evaluation of a repeated schedule is the ordered product of the block
evaluations. -/
lemma eval_repeat
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type*} [Group G] :
    ∀ (k : ℕ) (a : Fin k → S.Arguments G),
      (S.repeatSchedule k).eval (S.repeatArguments k a) =
        (List.ofFn fun i => S.eval (a i)).prod
  | 0, _ => by
      simp [repeatSchedule, repeatArguments, eval]
  | k + 1, a => by
      change
        (S.append (S.repeatSchedule k)).eval
            (S.appendArguments (S.repeatSchedule k)
              (a 0) (S.repeatArguments k fun i => a i.succ)) =
          (List.ofFn fun i => S.eval (a i)).prod
      rw [eval_append, eval_repeat]
      rw [List.ofFn_succ]
      simp

/-- A list of selected slot values is represented by one repeated schedule
block per list entry. -/
lemma repeat_arguments_prod
    {p d n : ℕ}
    (S : ZWSched p d n)
    {G : Type*} [Group G]
    (L : List (Σ i : Fin S.width, Fin (S.slot i).arity → G)) :
    ∃ a : (S.repeatSchedule L.length).Arguments G,
      (S.repeatSchedule L.length).eval a =
        (L.map fun z => (S.slot z.1).eval z.2).prod := by
  refine
    ⟨S.repeatArguments L.length
        (fun i => S.singleArguments (L.get i)), ?_⟩
  rw [eval_repeat]
  rw [← List.ofFn_get L, List.map_ofFn]
  simp [Function.comp_def, eval_singleArguments]

/-- A bounded-length list of selected slot values is represented by a fixed
number of repeated blocks, padding the unused suffix by identities. -/
lemma repeat_schedule_arguments
    {p d n k : ℕ}
    (S : ZWSched p d n)
    {G : Type*} [Group G]
    (L : List (Σ i : Fin S.width, Fin (S.slot i).arity → G))
    (hL : L.length ≤ k) :
    ∃ a : (S.repeatSchedule k).Arguments G,
      (S.repeatSchedule k).eval a =
        (L.map fun z => (S.slot z.1).eval z.2).prod := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hL
  refine
    ⟨S.repeatArguments (L.length + m)
        (Fin.append
          (fun i => S.singleArguments (L.get i))
          (fun _ : Fin m => S.oneArguments G)), ?_⟩
  rw [eval_repeat]
  have hvalues :
      (fun i =>
        S.eval
          (Fin.append
            (fun i => S.singleArguments (L.get i))
            (fun _ : Fin m => S.oneArguments G)
            i)) =
        Fin.append
        (fun i => S.eval (S.singleArguments (L.get i)))
        (fun _ : Fin m => S.eval (S.oneArguments G)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> simp
  rw [hvalues]
  rw [List.ofFn_fin_append, List.prod_append]
  rw [← List.ofFn_get L, List.map_ofFn]
  simp [Function.comp_def, eval_singleArguments, eval_oneArguments]

end ZWSched

/-- An atomic scheme for a literal `p ^ e`th power lying in `D_n`. -/
def zassenhausSchemeTail
    (p n e : ℕ)
    (hne : n ≤ p ^ e) :
    ZWScheme p n where
  arity := 1
  word := .atom 0
  frobenius := e
  level_bound := by
    simpa using hne

namespace CWord

/-- Put two freshly indexed commutator words below a new commutator node. -/
def finAppend
    {k l : ℕ}
    (u : CWord (Fin k))
    (v : CWord (Fin l)) :
    CWord (Fin (k + l)) :=
  .commutator
    (u.bind fun i => .atom (Fin.castAdd l i))
    (v.bind fun i => .atom (Fin.natAdd k i))

@[simp]
lemma eval_finAppend
    {k l : ℕ}
    {G : Type*} [Group G]
    (u : CWord (Fin k))
    (v : CWord (Fin l))
    (a : Fin k → G)
    (b : Fin l → G) :
    (finAppend u v).eval (Fin.addCases a b) =
      ⁅u.eval a, v.eval b⁆ := by
  simp [finAppend, CWord.eval_bind]

@[simp]
lemma weight_finAppend
    {k l : ℕ}
    (u : CWord (Fin k))
    (v : CWord (Fin l)) :
    (finAppend u v).weight (fun _ => 1) =
      u.weight (fun _ => 1) + v.weight (fun _ => 1) := by
  simp [finAppend, CWord.weight_bind]

/-- A raw commutator value can be represented with any positive number of
fresh atomic slots not exceeding its leaf weight.  Low subtrees are absorbed
as atomic arguments; no group identity is used beyond evaluation of the
binary tree. -/
lemma fin_abstraction_pos
    {α G : Type*} [Group G]
    (f : α → G) :
    ∀ (w : CWord α) (k : ℕ),
      0 < k →
        k ≤ w.weight (fun _ => 1) →
          ∃ v : CWord (Fin k),
            ∃ a : Fin k → G,
              v.eval a = w.eval f ∧
                v.weight (fun _ => 1) = k
  | .atom i, k, hkpos, hkle => by
      have hk : k = 1 := by
        have hkLeOne : k ≤ 1 := by
          simpa [CWord.weight] using hkle
        omega
      subst k
      exact ⟨.atom 0, fun _ => f i, rfl, rfl⟩
  | .commutator u v, k, hkpos, hkle => by
      by_cases hk : k = 1
      · subst k
        exact
          ⟨.atom 0,
            fun _ => ⁅u.eval f, v.eval f⁆,
            rfl,
            rfl⟩
      · have hkTwo : 2 ≤ k := by omega
        let ku : ℕ := min (u.weight (fun _ => 1)) (k - 1)
        let kv : ℕ := k - ku
        have huPos : 0 < u.weight (fun _ => 1) :=
          CWord.weight_pos (fun _ => 1) (fun _ => by simp) u
        have hvPos : 0 < v.weight (fun _ => 1) :=
          CWord.weight_pos (fun _ => 1) (fun _ => by simp) v
        have hkuPos : 0 < ku := by
          dsimp [ku]
          exact lt_min huPos (by omega)
        have hkuLe : ku ≤ u.weight (fun _ => 1) := by
          dsimp [ku]
          exact Nat.min_le_left _ _
        have hkuLePred : ku ≤ k - 1 := by
          dsimp [ku]
          exact Nat.min_le_right _ _
        have hkvPos : 0 < kv := by
          dsimp [kv]
          omega
        have hkvLe : kv ≤ v.weight (fun _ => 1) := by
          dsimp [kv, ku]
          rw [CWord.weight_commutator] at hkle
          by_cases hu : u.weight (fun _ => 1) ≤ k - 1
          · rw [Nat.min_eq_left hu]
            omega
          · rw [Nat.min_eq_right (Nat.le_of_not_ge hu)]
            omega
        obtain ⟨u', au, heu, hwu⟩ :=
          fin_abstraction_pos f u ku hkuPos hkuLe
        obtain ⟨v', av, hev, hwv⟩ :=
          fin_abstraction_pos f v kv hkvPos hkvLe
        have hsum : ku + kv = k := by
          dsimp [kv]
          omega
        rw [← hsum]
        refine ⟨finAppend u' v', Fin.addCases au av, ?_, ?_⟩
        · simp [heu, hev]
        · simp [hwu, hwv]

/-- If a raw powered commutator meets level `n > 0`, its base word can be
abstracted to at most `n` slots without changing its value or losing the
weighted level inequality. -/
lemma bounded_abstraction_level
    {α G : Type*} [Group G]
    (p n e : ℕ)
    (hn : 0 < n)
    (f : α → G)
    (w : CWord α)
    (hlevel : n ≤ w.weight (fun _ => 1) * p ^ e) :
    ∃ k : ℕ,
      0 < k ∧
        k ≤ n ∧
          ∃ v : CWord (Fin k),
            ∃ a : Fin k → G,
              v.eval a = w.eval f ∧
                v.weight (fun _ => 1) = k ∧
                  n ≤ k * p ^ e := by
  let k : ℕ := min n (w.weight fun _ => 1)
  have hwPos : 0 < w.weight (fun _ => 1) :=
    CWord.weight_pos (fun _ => 1) (fun _ => by simp) w
  have hkPos : 0 < k := by
    dsimp [k]
    exact lt_min hn hwPos
  have hkLeN : k ≤ n := by
    dsimp [k]
    exact Nat.min_le_left _ _
  have hkLeW : k ≤ w.weight (fun _ => 1) := by
    dsimp [k]
    exact Nat.min_le_right _ _
  obtain ⟨v, a, heval, hweight⟩ :=
    fin_abstraction_pos f w k hkPos hkLeW
  refine ⟨k, hkPos, hkLeN, v, a, heval, hweight, ?_⟩
  dsimp [k]
  by_cases hnw : n ≤ w.weight (fun _ => 1)
  · rw [Nat.min_eq_left hnw]
    have hpowNe : p ^ e ≠ 0 := by
      intro hp
      rw [hp, Nat.mul_zero] at hlevel
      omega
    calc
      n = n * 1 := by omega
      _ ≤ n * p ^ e :=
        Nat.mul_le_mul_left n (Nat.one_le_iff_ne_zero.mpr hpowNe)
  · rw [Nat.min_eq_right (Nat.le_of_not_ge hnw)]
    exact hlevel

/-- Recursively enumerate a finite over-approximation to the commutator words
of leaf weight at most `budget` over a finite alphabet. -/
def finiteAlphabetWords
    {α : Type*}
    (atoms : List α) :
    ℕ → List (CWord α)
  | 0 => []
  | budget + 1 =>
      atoms.map .atom ++
        (finiteAlphabetWords atoms budget).flatMap fun u =>
          (finiteAlphabetWords atoms budget).map fun v =>
            .commutator u v

/-- Every word of leaf weight at most `budget` occurs in the finite recursive
enumeration when every atom occurs in the supplied alphabet. -/
lemma alphabet_words_weight
    {α : Type*}
    (atoms : List α)
    (hatoms : ∀ a : α, a ∈ atoms) :
    ∀ (w : CWord α) (budget : ℕ),
      w.weight (fun _ => 1) ≤ budget →
        w ∈ finiteAlphabetWords atoms budget
  | .atom a, 0, h => by
      simp [CWord.weight] at h
  | .atom a, budget + 1, _ => by
      simp [finiteAlphabetWords, hatoms a]
  | .commutator u v, 0, h => by
      have huPos : 0 < u.weight (fun _ => 1) :=
        CWord.weight_pos (fun _ => 1) (fun _ => by simp) u
      have hvPos : 0 < v.weight (fun _ => 1) :=
        CWord.weight_pos (fun _ => 1) (fun _ => by simp) v
      simp [CWord.weight] at h
      omega
  | .commutator u v, budget + 1, h => by
      have huPos : 0 < u.weight (fun _ => 1) :=
        CWord.weight_pos (fun _ => 1) (fun _ => by simp) u
      have hvPos : 0 < v.weight (fun _ => 1) :=
        CWord.weight_pos (fun _ => 1) (fun _ => by simp) v
      have huLe : u.weight (fun _ => 1) ≤ budget := by
        rw [CWord.weight_commutator] at h
        omega
      have hvLe : v.weight (fun _ => 1) ≤ budget := by
        rw [CWord.weight_commutator] at h
        omega
      simp only [finiteAlphabetWords, List.mem_append, List.mem_flatMap,
        List.mem_map]
      right
      exact
        ⟨u,
          alphabet_words_weight atoms hatoms u budget huLe,
          v,
          alphabet_words_weight atoms hatoms v budget hvLe,
          rfl⟩

/-- Relabel a word along the standard inclusion of a smaller `Fin` alphabet
into a larger one. -/
def castLE
    {k n : ℕ}
    (h : k ≤ n)
    (w : CWord (Fin k)) :
    CWord (Fin n) :=
  w.bind fun i => .atom (Fin.castLE h i)

@[simp]
lemma eval_castLE
    {k n : ℕ}
    (h : k ≤ n)
    {G : Type*} [Group G]
    (w : CWord (Fin k))
    (a : Fin n → G) :
    (castLE h w).eval a =
      w.eval fun i => a (Fin.castLE h i) := by
  simp [castLE]

@[simp]
lemma weight_castLE
    {k n : ℕ}
    (h : k ≤ n)
    (w : CWord (Fin k)) :
    (castLE h w).weight (fun _ => 1) =
      w.weight (fun _ => 1) := by
  simp [castLE]

end CWord

/-- Every powered commutator value at positive Zassenhaus level has a scheme
representative with bounded arity and bounded Frobenius exponent.  When the
original exponent is already large enough, its excess is absorbed into the
single atomic argument. -/
lemma bounded_scheme_commutator
    {α G : Type*} [Group G]
    (p n e : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (f : α → G)
    (w : CWord α)
    (hlevel : n ≤ w.weight (fun _ => 1) * p ^ e) :
    ∃ S : ZWScheme p n,
      S.arity ≤ n ∧
        S.frobenius ≤ leastPrimeExponent p n ∧
          S.word.weight (fun _ => 1) ≤ n ∧
          ∃ a : Fin S.arity → G,
            S.eval a = w.eval f ^ (p ^ e) := by
  by_cases he : e ≤ leastPrimeExponent p n
  · obtain ⟨k, _hkPos, hkLeN, v, a, heval, hweight, hkLevel⟩ :=
      CWord.bounded_abstraction_level
        p n e hn f w hlevel
    let S : ZWScheme p n :=
      { arity := k
        word := v
        frobenius := e
        level_bound := by
          simpa [hweight] using hkLevel }
    refine ⟨S, hkLeN, he, by simpa [S, hweight] using hkLeN, a, ?_⟩
    simp [S, ZWScheme.eval, heval]
  · have hleastLe : leastPrimeExponent p n ≤ e :=
      Nat.le_of_not_ge he
    obtain ⟨r, rfl⟩ :=
      Nat.exists_eq_add_of_le hleastLe
    let S : ZWScheme p n :=
      zassenhausSchemeTail
        p n (leastPrimeExponent p n)
        (pow_least_exponent p n)
    have hSWeightLe : S.word.weight (fun _ => 1) ≤ n := by
      change 1 ≤ n
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
    refine
      ⟨S,
        hSWeightLe,
        le_rfl,
        hSWeightLe,
        fun _ => w.eval f ^ (p ^ r),
        ?_⟩
    simp [S, zassenhausSchemeTail, ZWScheme.eval,
      pow_add, pow_mul, Nat.mul_comm]

/-- Extend a tuple of arguments along the standard inclusion `Fin k → Fin n`,
using an arbitrary fallback outside the image. -/
def extendFinArguments
    {k n : ℕ}
    (_h : k ≤ n)
    {G : Type*}
    (a : Fin k → G)
    (fallback : G) :
    Fin n → G :=
  fun i =>
    if hi : i.val < k then
      a ⟨i.val, hi⟩
    else
      fallback

@[simp]
lemma extend_arguments_cast
    {k n : ℕ}
    (h : k ≤ n)
    {G : Type*}
    (a : Fin k → G)
    (fallback : G)
    (i : Fin k) :
    extendFinArguments h a fallback (Fin.castLE h i) = a i := by
  simp [extendFinArguments, Fin.castLE]

/-- Pad a scheme of arity at most `n` to the common arity `n`. -/
def ZWScheme.padArity
    {p n : ℕ}
    (S : ZWScheme p n)
    (h : S.arity ≤ n) :
    ZWScheme p n where
  arity := n
  word := S.word.castLE h
  frobenius := S.frobenius
  level_bound := by
    simpa using S.level_bound

@[simp]
lemma ZWScheme.padArity_eval
    {p n : ℕ}
    (S : ZWScheme p n)
    (h : S.arity ≤ n)
    {G : Type*} [Group G]
    (a : Fin S.arity → G)
    (fallback : G) :
    (S.padArity h).eval (extendFinArguments h a fallback) =
      S.eval a := by
  simp [ZWScheme.padArity, ZWScheme.eval]

/-- The finite list of fixed-arity tree/exponent pairs that satisfy the
requested Zassenhaus level inequality. -/
noncomputable def boundedZassenhausPairs
    (p n : ℕ) [Fact p.Prime] :
    List (CWord (Fin n) × ℕ) :=
  ((CWord.finiteAlphabetWords (List.ofFn fun i : Fin n => i) n).product
      (List.range (leastPrimeExponent p n + 1))).filter fun q =>
        decide (n ≤ q.1.weight (fun _ => 1) * p ^ q.2)

lemma bounded_zassenhaus_pairs
    (p n : ℕ) [Fact p.Prime]
    (w : CWord (Fin n))
    (e : ℕ)
    (hw :
      w ∈ CWord.finiteAlphabetWords
        (List.ofFn fun i : Fin n => i) n)
    (he : e ≤ leastPrimeExponent p n)
    (hlevel : n ≤ w.weight (fun _ => 1) * p ^ e) :
    (w, e) ∈ boundedZassenhausPairs p n := by
  simp [boundedZassenhausPairs, hw, Nat.lt_succ_iff.mpr he, hlevel]

/-- Turn an attached admissible fixed-arity pair into a scheme. -/
def schemeBoundedPair
    (p n : ℕ) [Fact p.Prime]
    (q : {q // q ∈ boundedZassenhausPairs p n}) :
    ZWScheme p n where
  arity := n
  word := q.1.1
  frobenius := q.1.2
  level_bound := by
    have h := (List.mem_filter.mp q.2).2
    exact of_decide_eq_true h

/-- The concrete finite family of normalized schemes. -/
noncomputable def boundedZassenhausSchemes
    (p n : ℕ) [Fact p.Prime] :
    List (ZWScheme p n) :=
  (boundedZassenhausPairs p n).attach.map fun q =>
    schemeBoundedPair p n q

/-- Every powered commutator value at positive level belongs to the range of
one member of the concrete finite normalized family. -/
lemma bounded_schemes_commutator
    {α G : Type*} [Group G]
    (p n e : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (f : α → G)
    (w : CWord α)
    (hlevel : n ≤ w.weight (fun _ => 1) * p ^ e) :
    ∃ S ∈ boundedZassenhausSchemes p n,
      ∃ a : Fin S.arity → G,
        S.eval a = w.eval f ^ (p ^ e) := by
  obtain ⟨S, hSarity, hSfrob, hSweight, a, heval⟩ :=
    bounded_scheme_commutator
      p n e hn f w hlevel
  let T : ZWScheme p n := S.padArity hSarity
  have hTword :
      T.word ∈
        CWord.finiteAlphabetWords
          (List.ofFn fun i : Fin n => i) n := by
    apply CWord.alphabet_words_weight
    · intro i
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · simpa [T, ZWScheme.padArity] using hSweight
  have hTpair :
      (T.word, T.frobenius) ∈ boundedZassenhausPairs p n := by
    apply bounded_zassenhaus_pairs
    · exact hTword
    · simpa [T, ZWScheme.padArity] using hSfrob
    · exact T.level_bound
  let q : {q // q ∈ boundedZassenhausPairs p n} :=
    ⟨(T.word, T.frobenius), hTpair⟩
  let U : ZWScheme p n :=
    schemeBoundedPair p n q
  refine ⟨U, ?_, extendFinArguments hSarity a 1, ?_⟩
  · simp [boundedZassenhausSchemes, U]
  · change T.eval (extendFinArguments hSarity a 1) = _
    rw [ZWScheme.padArity_eval]
    exact heval

/-- Use the concrete normalized scheme list as a schedule. -/
noncomputable def boundedZassenhausSchedule
    (p d n : ℕ) [Fact p.Prime] :
    ZWSched p d n where
  width := (boundedZassenhausSchemes p n).length
  slot := fun i => (boundedZassenhausSchemes p n).get i

/-- Membership in the normalized finite list is equivalent to occurrence as
one slot of the normalized schedule. -/
lemma bounded_schedule_slot
    (p d n : ℕ) [Fact p.Prime]
    {S : ZWScheme p n}
    (hS : S ∈ boundedZassenhausSchemes p n) :
    ∃ i : Fin (boundedZassenhausSchedule p d n).width,
      (boundedZassenhausSchedule p d n).slot i = S := by
  simpa [boundedZassenhausSchedule] using List.get_of_mem hS

/-- Every powered commutator value at positive level is the value of one slot
in the concrete normalized schedule. -/
lemma bounded_slot_commutator
    {α G : Type*} [Group G]
    (p d n e : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (f : α → G)
    (w : CWord α)
    (hlevel : n ≤ w.weight (fun _ => 1) * p ^ e) :
    ∃ i : Fin (boundedZassenhausSchedule p d n).width,
      ∃ a : Fin ((boundedZassenhausSchedule p d n).slot i).arity → G,
        ((boundedZassenhausSchedule p d n).slot i).eval a =
          w.eval f ^ (p ^ e) := by
  obtain ⟨S, hS, a, heval⟩ :=
    bounded_schemes_commutator
      p n e hn f w hlevel
  obtain ⟨i, hi⟩ :=
    bounded_schedule_slot p d n hS
  subst S
  exact ⟨i, a, heval⟩

namespace CWord

/-- Conjugating every atomic argument conjugates the value of the whole
commutator word. -/
lemma eval_conjugate
    {α G : Type*} [Group G]
    (c : G)
    (f : α → G) :
    ∀ w : CWord α,
      w.eval (fun i => c * f i * c⁻¹) =
        c * w.eval f * c⁻¹
  | .atom _ => rfl
  | .commutator u v => by
      simp only [CWord.eval_commutator, eval_conjugate c f u,
        eval_conjugate c f v, commutatorElement_def]
      group

/-- The inverse of a commutator-word value is again a commutator-word value of
the same leaf weight, possibly over a fresh one-letter alphabet in the atomic
case. -/
lemma eval_inv_weight
    {α G : Type*} [Group G]
    (f : α → G) :
    ∀ w : CWord α,
      ∃ g : Option α → G,
        ∃ v : CWord (Option α),
          v.eval g = (w.eval f)⁻¹ ∧
            v.weight (fun _ => 1) = w.weight (fun _ => 1)
  | .atom i =>
      ⟨fun
          | none => (f i)⁻¹
          | some j => f j,
        .atom none,
        rfl,
        rfl⟩
  | .commutator u v => by
      let g : Option α → G :=
        fun
          | none => 1
          | some i => f i
      let embed : α → CWord (Option α) :=
        fun i => .atom (some i)
      refine
        ⟨g,
          (CWord.commutator v u).bind embed,
          ?_,
          ?_⟩
      · simp [g, embed, commutatorElement_inv]
      · simp [embed, Nat.add_comm]

end CWord

/-- The normalized schedule covers conjugates of powered commutator values. -/
lemma slot_conjugate_commutator
    {α G : Type*} [Group G]
    (p d n e : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (c : G)
    (f : α → G)
    (w : CWord α)
    (hlevel : n ≤ w.weight (fun _ => 1) * p ^ e) :
    ∃ i : Fin (boundedZassenhausSchedule p d n).width,
      ∃ a : Fin ((boundedZassenhausSchedule p d n).slot i).arity → G,
        ((boundedZassenhausSchedule p d n).slot i).eval a =
          c * (w.eval f ^ (p ^ e)) * c⁻¹ := by
  obtain ⟨i, a, ha⟩ :=
    bounded_slot_commutator
      p d n e hn (fun j => c * f j * c⁻¹) w hlevel
  refine ⟨i, a, ?_⟩
  rw [ha, CWord.eval_conjugate]
  simp

/-- The normalized schedule covers inverses of powered commutator values. -/
lemma slot_inv_commutator
    {α G : Type*} [Group G]
    (p d n e : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (f : α → G)
    (w : CWord α)
    (hlevel : n ≤ w.weight (fun _ => 1) * p ^ e) :
    ∃ i : Fin (boundedZassenhausSchedule p d n).width,
      ∃ a : Fin ((boundedZassenhausSchedule p d n).slot i).arity → G,
        ((boundedZassenhausSchedule p d n).slot i).eval a =
          (w.eval f ^ (p ^ e))⁻¹ := by
  obtain ⟨g, v, heval, hweight⟩ :=
    CWord.eval_inv_weight f w
  have hvLevel : n ≤ v.weight (fun _ => 1) * p ^ e := by
    simpa [hweight] using hlevel
  obtain ⟨i, a, ha⟩ :=
    bounded_slot_commutator
      p d n e hn g v hvLevel
  refine ⟨i, a, ?_⟩
  rw [ha, heval]
  simp

/-- One selected value from the concrete normalized schedule. -/
abbrev BSValue
    (p d n : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] :=
  Σ i : Fin (boundedZassenhausSchedule p d n).width,
    Fin ((boundedZassenhausSchedule p d n).slot i).arity → G

/-- Evaluate one selected normalized schedule value. -/
def BSValue.eval
    {p d n : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (z : BSValue p d n G) :
    G :=
  ((boundedZassenhausSchedule p d n).slot z.1).eval z.2

/-- A bounded list of normalized values is absorbed by a fixed repetition of
the normalized schedule, with identities filling the unused blocks. -/
lemma repeat_arguments_length
    {p d n k : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (L : List (BSValue p d n G))
    (hL : L.length ≤ k) :
    ∃ a :
        ((boundedZassenhausSchedule p d n).repeatSchedule k).Arguments G,
      ((boundedZassenhausSchedule p d n).repeatSchedule k).eval a =
        (L.map BSValue.eval).prod := by
  simpa [BSValue.eval] using
    ZWSched.repeat_schedule_arguments
      (boundedZassenhausSchedule p d n) L hL

/-- The remaining uniform-width statement after normalizing all admissible
Zassenhaus factors to the concrete bounded schedule. -/
def BoundedNormalizedList
    (p d n k : ℕ) [Fact p.Prime] :
    Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q],
    IsPGroup p Q →
      ∀ t : Fin d → Q,
        GeneratedBy t →
          ∀ x : Q,
            x ∈ zassenhausFiltration p Q n →
              ∃ L : List (BSValue p d n Q),
                L.length ≤ k ∧
                  (L.map BSValue.eval).prod = x

/-- A quotient-independent normalized-list bound packages into the requested
finite schedule by repeating the normalized block and padding with identities. -/
theorem collection_normalized_list
    {p d n k : ℕ} [Fact p.Prime]
    (h : BoundedNormalizedList.{u} p d n k) :
    Nonempty (FSColl.{u} p d n) := by
  refine ⟨{
    schedule := (boundedZassenhausSchedule p d n).repeatSchedule k
    factor := ?_ }⟩
  intro Q _ _ hQ t ht x hx
  obtain ⟨L, hL, hprod⟩ := h Q hQ t ht x hx
  obtain ⟨a, ha⟩ :=
    repeat_arguments_length
      L hL
  exact ⟨a, ha.trans hprod⟩

/-- A weighted powered-commutator factor, including its outer conjugator and
integral multiplicity, expands to a finite list of values from the normalized
schedule. -/
lemma bounded_scheduled_weighted
    {α G : Type*} [Group G]
    (p d n : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (f : α → G)
    (F :
      WCFactor p f (fun _ => 1) n) :
    ∃ L : List (BSValue p d n G),
      (L.map BSValue.eval).prod = F.eval := by
  cases hmult : F.multiplicity with
  | ofNat m =>
      obtain ⟨i, a, ha⟩ :=
        slot_conjugate_commutator
          p d n F.primeExponent hn F.conjugator f F.word F.weight_bound
      let z : BSValue p d n G := ⟨i, a⟩
      refine ⟨List.replicate m z, ?_⟩
      simp [z, BSValue.eval, ha,
        WCFactor.eval, hmult]
  | negSucc m =>
      obtain ⟨i, a, ha⟩ :=
        slot_inv_commutator
          p d n F.primeExponent hn
            (fun j => F.conjugator * f j * F.conjugator⁻¹)
            F.word
            F.weight_bound
      let z : BSValue p d n G := ⟨i, a⟩
      refine ⟨List.replicate (m + 1) z, ?_⟩
      have hz :
          z.eval =
            F.conjugator *
                (F.word.eval f ^ (p ^ F.primeExponent))⁻¹ *
              F.conjugator⁻¹ := by
        dsimp [z, BSValue.eval]
        rw [ha, CWord.eval_conjugate, conj_pow]
        group
      rw [List.map_replicate, List.prod_replicate, hz, conj_pow]
      simp [WCFactor.eval, hmult, inv_pow]

/-- The normalized expansion of one admitted weighted factor uses exactly the
absolute value of its residual integral multiplicity. -/
lemma scheduled_weighted_length
    {α G : Type*} [Group G]
    (p d n : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (f : α → G)
    (F :
      WCFactor p f (fun _ => 1) n) :
    ∃ L : List (BSValue p d n G),
      (L.map BSValue.eval).prod = F.eval ∧
        L.length = F.multiplicity.natAbs := by
  cases hmult : F.multiplicity with
  | ofNat m =>
      obtain ⟨i, a, ha⟩ :=
        slot_conjugate_commutator
          p d n F.primeExponent hn F.conjugator f F.word F.weight_bound
      let z : BSValue p d n G := ⟨i, a⟩
      refine ⟨List.replicate m z, ?_, ?_⟩
      · simp [z, BSValue.eval, ha,
          WCFactor.eval, hmult]
      · simp
  | negSucc m =>
      obtain ⟨i, a, ha⟩ :=
        slot_inv_commutator
          p d n F.primeExponent hn
            (fun j => F.conjugator * f j * F.conjugator⁻¹)
            F.word
            F.weight_bound
      let z : BSValue p d n G := ⟨i, a⟩
      refine ⟨List.replicate (m + 1) z, ?_, ?_⟩
      · have hz :
            z.eval =
              F.conjugator *
                  (F.word.eval f ^ (p ^ F.primeExponent))⁻¹ *
                F.conjugator⁻¹ := by
          dsimp [z, BSValue.eval]
          rw [ha, CWord.eval_conjugate, conj_pow]
          group
        rw [List.map_replicate, List.prod_replicate, hz, conj_pow]
        simp [WCFactor.eval, hmult, inv_pow]
      · simp

/-- A collected list of weighted powered-commutator factors expands to a
single finite list of values from the normalized schedule. -/
lemma scheduled_value_weighted
    {α G : Type*} [Group G]
    (p d n : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (f : α → G) :
    ∀ L : List (WCFactor p f (fun _ => 1) n),
      ∃ M : List (BSValue p d n G),
        (M.map BSValue.eval).prod =
          WCFactor.listEval L
  | [] => ⟨[], rfl⟩
  | F :: L => by
      obtain ⟨MF, hMF⟩ :=
        bounded_scheduled_weighted
          p d n hn f F
      obtain ⟨ML, hML⟩ :=
        scheduled_value_weighted
          p d n hn f L
      refine ⟨MF ++ ML, ?_⟩
      simp [hMF, hML]

/-- Every element of a weighted powered-commutator subgroup with unit atomic
weights is a finite product of values from the explicit normalized schedule. -/
lemma scheduled_weighted_power
    {α G : Type*} [Group G]
    (p d n : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (f : α → G)
    {x : G}
    (hx :
      x ∈ weightedCommutatorSubgroup p f (fun _ => 1) n) :
    ∃ M : List (BSValue p d n G),
      (M.map BSValue.eval).prod = x := by
  obtain ⟨L, hL⟩ :=
    WCFactor.list_eval hx
  obtain ⟨M, hM⟩ :=
    scheduled_value_weighted
      p d n hn f L
  exact ⟨M, hM.trans hL⟩

/-- The alphabet of arbitrary lower-central elements, carrying their
one-based lower-central weights. -/
abbrev LCAtom
    (G : Type*) [Group G] :=
  Σ i : ℕ, Subgroup.lowerCentralSeries G i

/-- Evaluate a weighted lower-central atom in the ambient group. -/
def LCAtom.eval
    {G : Type*} [Group G]
    (a : LCAtom G) :
    G :=
  a.2

/-- The one-based lower-central weight of an atom. -/
def LCAtom.weight
    {G : Type*} [Group G]
    (a : LCAtom G) :
    ℕ :=
  a.1 + 1

lemma LCAtom.weight_pos
    {G : Type*} [Group G]
    (a : LCAtom G) :
    0 < a.weight := by
  simp [LCAtom.weight]

lemma LCAtom.eval_lower_series
    {G : Type*} [Group G]
    (a : LCAtom G) :
    a.eval ∈ Subgroup.lowerCentralSeries G (a.weight - 1) := by
  simp [LCAtom.eval, LCAtom.weight]

/-- The explicit Zassenhaus filtration is exactly the weighted powered-word
subgroup on the alphabet of arbitrary lower-central atoms. -/
lemma weighted_atom_filtration
    (p : ℕ)
    (G : Type*) [Group G]
    (n : ℕ) :
    weightedCommutatorSubgroup
        p
        (LCAtom.eval : LCAtom G → G)
        LCAtom.weight
        n =
      zassenhausFiltration p G n := by
  apply le_antisymm
  · exact
      weighted_commutator_filtration
        (LCAtom.eval : LCAtom G → G)
        LCAtom.weight
        LCAtom.weight_pos
        LCAtom.eval_lower_series
        n
  · rw [zassenhausFiltration]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, e, x, hx, hlevel, rfl⟩
    let a : LCAtom G := ⟨i, ⟨x, hx⟩⟩
    have ha :
        (CWord.atom a).eval
              (LCAtom.eval : LCAtom G → G) ^
            (p ^ e) ∈
          weightedCommutatorSubgroup
            p
            (LCAtom.eval : LCAtom G → G)
            LCAtom.weight
            n := by
      apply
        CWord.evalpowprime_powermemweight_powcomworsub
      simpa [a, LCAtom.weight] using hlevel
    simpa [a, LCAtom.eval] using ha

/-- The range of all selected values of the explicit bounded schedule. -/
def boundedScheduledSet
    (p d n : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] :
    Set G :=
  {x : G |
    ∃ z : BSValue p d n G,
      z.eval = x}

/-- The normalized value range is inverse-closed at positive depth. -/
lemma bounded_scheduled_inv
    {p d n : ℕ} [Fact p.Prime]
    (hn : 0 < n)
    {G : Type*} [Group G]
    {x : G}
    (hx : x ∈ boundedScheduledSet p d n G) :
    x⁻¹ ∈ boundedScheduledSet p d n G := by
  rcases hx with ⟨z, rfl⟩
  let S := (boundedZassenhausSchedule p d n).slot z.1
  let w : CWord G :=
    S.word.bind fun i => .atom (z.2 i)
  have hw :
      n ≤ w.weight (fun _ => 1) * p ^ S.frobenius := by
    simpa [w, S] using S.level_bound
  obtain ⟨i, a, ha⟩ :=
    slot_inv_commutator
      p d n S.frobenius hn (fun x : G => x) w hw
  refine ⟨⟨i, a⟩, ?_⟩
  simpa [BSValue.eval, S, w,
    ZWScheme.eval, CWord.eval_bind] using ha

/-- The normalized value range is closed under conjugation at positive depth. -/
lemma bounded_scheduled_conj
    {p d n : ℕ} [Fact p.Prime]
    (hn : 0 < n)
    {G : Type*} [Group G]
    {x : G}
    (hx : x ∈ boundedScheduledSet p d n G)
    (c : G) :
    c * x * c⁻¹ ∈ boundedScheduledSet p d n G := by
  rcases hx with ⟨z, rfl⟩
  let S := (boundedZassenhausSchedule p d n).slot z.1
  let w : CWord G :=
    S.word.bind fun i => .atom (z.2 i)
  have hw :
      n ≤ w.weight (fun _ => 1) * p ^ S.frobenius := by
    simpa [w, S] using S.level_bound
  obtain ⟨i, a, ha⟩ :=
    slot_conjugate_commutator
      p d n S.frobenius hn c (fun x : G => x) w hw
  refine ⟨⟨i, a⟩, ?_⟩
  simpa [BSValue.eval, S, w,
    ZWScheme.eval, CWord.eval_bind] using ha

/-- Taking all conjugates does not enlarge the normalized value range. -/
lemma conjugates_scheduled_value
    (p d n : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (G : Type*) [Group G] :
    Group.conjugatesOfSet (boundedScheduledSet p d n G) =
      boundedScheduledSet p d n G := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨_, hz, hconj⟩
    rcases isConj_iff.mp hconj with ⟨c, rfl⟩
    exact bounded_scheduled_conj hn hz c
  · exact Group.subset_conjugatesOfSet

/-- The normal closure generated by all selected values of the explicit
bounded schedule. -/
def boundedScheduleSubgroup
    (p d n : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] :
    Subgroup G :=
  Subgroup.normalClosure (boundedScheduledSet p d n G)

/-- At positive depth the normalized range is already conjugation-stable, so
its normal closure is its subgroup closure. -/
lemma bounded_schedule_closure
    (p d n : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (G : Type*) [Group G] :
    boundedScheduleSubgroup p d n G =
      Subgroup.closure (boundedScheduledSet p d n G) := by
  rw [boundedScheduleSubgroup, Subgroup.normalClosure,
    conjugates_scheduled_value p d n hn G]

lemma BSValue.mem_scheduleSubgroup
    {p d n : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (z : BSValue p d n G) :
    z.eval ∈ boundedScheduleSubgroup p d n G := by
  exact Subgroup.subset_normalClosure ⟨z, rfl⟩

lemma scheduled_schedule_subgroup
    {p d n : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] :
    ∀ L : List (BSValue p d n G),
      (L.map BSValue.eval).prod ∈
        boundedScheduleSubgroup p d n G
  | [] => by simp
  | z :: L => by
      simpa using
        (boundedScheduleSubgroup p d n G).mul_mem
          z.mem_scheduleSubgroup
          (scheduled_schedule_subgroup L)

/-- Unit-weight powered commutator words generate exactly the same normal
subgroup as the explicit bounded schedule ranges. -/
lemma bounded_weighted_id
    (p d n : ℕ) [Fact p.Prime]
    (hn : 0 < n)
    (G : Type*) [Group G] :
    boundedScheduleSubgroup p d n G =
      weightedCommutatorSubgroup p (fun x : G => x) (fun _ => 1) n := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨z, rfl⟩
    let S := (boundedZassenhausSchedule p d n).slot z.1
    let w : CWord G :=
      S.word.bind fun i => .atom (z.2 i)
    have hw :
        n ≤ w.weight (fun _ => 1) * p ^ S.frobenius := by
      simpa [w, S] using S.level_bound
    have hmem :
        w.eval (fun x : G => x) ^ (p ^ S.frobenius) ∈
          weightedCommutatorSubgroup
            p (fun x : G => x) (fun _ => 1) n :=
      CWord.evalpowprime_powermemweight_powcomworsub
        hw
    simpa [BSValue.eval, S, w,
      ZWScheme.eval] using hmem
  · intro x hx
    obtain ⟨M, hM⟩ :=
      scheduled_weighted_power
        p d n hn (fun x : G => x) hx
    rw [← hM]
    exact scheduled_schedule_subgroup M

/-- Commuting a high-weight unit-atom word subgroup with an arbitrary group
element raises the leaf-weight cutoff by one. -/
lemma high_top_succ
    (G : Type*) [Group G]
    (cutoff : ℕ) :
    ⁅highCommutatorSubgroup (fun x : G => x) (fun _ => 1) cutoff,
        (⊤ : Subgroup G)⁆ ≤
      highCommutatorSubgroup
        (fun x : G => x) (fun _ => 1) (cutoff + 1) := by
  let H :=
    highCommutatorSubgroup (fun x : G => x) (fun _ => 1) cutoff
  let N :=
    highCommutatorSubgroup
      (fun x : G => x) (fun _ => 1) (cutoff + 1)
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let K : Subgroup G := (Subgroup.center (G ⧸ N)).comap q
  have hHK : H ≤ K := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨w, hw, rfl⟩
    change q (w.eval fun x : G => x) ∈ Subgroup.center (G ⧸ N)
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hbound :
        cutoff + 1 ≤
          (CWord.commutator (.atom g) w).weight (fun _ => 1) := by
      simpa [Nat.add_comm] using Nat.add_le_add_left hw 1
    simpa [N] using
      (CWord.evalmem_highweight_commwordsubg
        (f := fun x : G => x)
        (wt := fun _ : G => 1)
        (w := CWord.commutator (.atom g) w)
        hbound)
  apply Subgroup.commutator_le.mpr
  intro x hx y _hy
  have hxK : x ∈ K := hHK hx
  have hxCenter : q x ∈ Subgroup.center (G ⧸ N) := by
    simpa [K] using hxK
  rw [← QuotientGroup.eq_one_iff]
  change q ⁅x, y⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp hxCenter (q y)).symm

/-- Every lower-central term is contained in the unit-atom high-weight word
subgroup at its expected one-based leaf cutoff. -/
lemma lower_high_id
    (G : Type*) [Group G] :
    ∀ i : ℕ,
      Subgroup.lowerCentralSeries G i ≤
        highCommutatorSubgroup
          (fun x : G => x) (fun _ => 1) (i + 1)
  | 0 => by
      intro x _hx
      exact
        CWord.evalmem_highweight_commwordsubg
          (w := .atom x)
          (by simp)
  | i + 1 => by
      rw [Subgroup.lowerCentralSeries_succ]
      exact
        (Subgroup.commutator_mono
            (lower_high_id G i)
            le_rfl).trans
          (high_top_succ G (i + 1))

/-- Every lower-central element is a finite product of values from the
normalized schedule at its expected one-based level. -/
lemma scheduled_value_series
    {G : Type*} [Group G]
    (p d i : ℕ) [Fact p.Prime]
    {x : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G i) :
    ∃ M : List (BSValue p d (i + 1) G),
      (M.map BSValue.eval).prod = x := by
  have hxHigh :
      x ∈
        highCommutatorSubgroup
          (fun x : G => x) (fun _ => 1) (i + 1) :=
    lower_high_id G i hx
  have hxWeighted :
      x ∈
        weightedCommutatorSubgroup
          p (fun x : G => x) (fun _ => 1) (i + 1) :=
    high_weighted_power
      p (fun x : G => x) (fun _ => 1) (i + 1) hxHigh
  exact
    scheduled_weighted_power
      p d (i + 1) (Nat.succ_pos i) (fun x : G => x) hxWeighted

/-- Increasing the cutoff can only shrink the weighted-power word subgroup. -/
lemma weighted_commutator_antitone
    (p : ℕ) {α G : Type*} [Group G]
    (f : α → G) (wt : α → ℕ) :
    Antitone (weightedCommutatorSubgroup p f wt) := by
  intro a b hab
  apply Subgroup.normalClosure_mono
  rintro _ ⟨w, e, hweight, rfl⟩
  exact ⟨w, e, hab.trans hweight, rfl⟩

/-- The raw powered-word generators for the unit-weight alphabet consisting of
all ambient group elements. -/
def unitWeightedSet
    (p n : ℕ)
    (G : Type*) [Group G] :
    Set G :=
  {x : G |
    ∃ (w : CWord G) (e : ℕ),
      n ≤ w.weight (fun _ => 1) * p ^ e ∧
        w.eval (fun x : G => x) ^ (p ^ e) = x}

lemma weighted_id_set
    (p n : ℕ)
    (G : Type*) [Group G] :
    weightedCommutatorSubgroup p (fun x : G => x) (fun _ => 1) n =
      Subgroup.normalClosure (unitWeightedSet p n G) := by
  rfl

/-- Conjugating a raw unit-weight generator only conjugates each of its atomic
arguments, so it remains a raw generator at the same cutoff. -/
lemma conjugates_set_generator
    (p n : ℕ)
    (G : Type*) [Group G] :
    Group.conjugatesOfSet (unitWeightedSet p n G) =
      unitWeightedSet p n G := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨_, ⟨w, e, hw, rfl⟩, hconj⟩
    rcases isConj_iff.mp hconj with ⟨c, rfl⟩
    let v : CWord G :=
      w.bind fun z => .atom (c * z * c⁻¹)
    refine ⟨v, e, ?_, ?_⟩
    · simpa [v, CWord.weight_bind] using hw
    · simp [v, CWord.eval_bind, CWord.eval_conjugate,
        conj_pow]
  · exact Group.subset_conjugatesOfSet

namespace PPColl
namespace Trace

/-- Transport a Hall-Petresco trace through a group homomorphism without
changing its ordered factor count. -/
def mapHom
    {p a b : ℕ}
    {G H : Type*} [Group G] [Group H]
    {x y : G}
    (φ : G →* H)
    (T : Trace p x y a b) :
    Trace p (φ x) (φ y) a b where
  factors := RFactor.listMapHom φ T.factors
  eval_eq := by
    rw [RFactor.list_eval_hom, T.eval_eq]
    simp only [map_commutatorElement, map_pow]
  factors_good := by
    intro F hF
    rcases List.mem_map.mp hF with ⟨E, hE, rfl⟩
    simpa using T.factors_good E hE

end Trace
end PPColl

/-- After substituting two weighted words into a good nonzero Hall factor, the
`p`-adic part of its coefficient pays for the requested combined cutoff. -/
lemma HPGood.leweighthall_paibinmulpri_powpadicvalnat
    {p a b cutoff : ℕ} [Fact p.Prime]
    {α : Type*}
    (wt : α → ℕ)
    (u v : CWord α)
    {w : CWord HPAtom}
    {c : ℤ}
    (hcutoff :
      cutoff ≤ u.weight wt * p ^ a + v.weight wt * p ^ b)
    (hc : c ≠ 0)
    (hgood : HPGood p a b w c) :
    cutoff ≤
      (CWord.hallPairBind u v w).weight wt *
        p ^ padicValNat p c.natAbs := by
  let e : ℕ := padicValNat p c.natAbs
  have hcAbs : c.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hc
  have hleft :
      p ^ a ≤ w.pairLeftDegree * p ^ e :=
    HPGood.padic_val_dvd
      hgood.1 hcAbs (by
        simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hgood.2.2.1)
  have hright :
      p ^ b ≤ w.pairRightDegree * p ^ e :=
    HPGood.padic_val_dvd
      hgood.2.1 hcAbs (by
        simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hgood.2.2.2)
  calc
    cutoff ≤ u.weight wt * p ^ a + v.weight wt * p ^ b :=
      hcutoff
    _ ≤
        u.weight wt * (w.pairLeftDegree * p ^ e) +
          v.weight wt * (w.pairRightDegree * p ^ e) :=
      Nat.add_le_add
        (Nat.mul_le_mul_left (u.weight wt) hleft)
        (Nat.mul_le_mul_left (v.weight wt) hright)
    _ =
        (CWord.hallPairBind u v w).weight wt * p ^ e := by
      rw [CWord.weight_pair_bind,
        w.pair_atom_degree]
      ring

namespace PPColl
namespace RFactor

/-- A nonzero good raw Hall factor becomes one admitted weighted factor after
substituting arbitrary commutator words for the Hall pair. -/
lemma weighted_good_ne
    {p a b cutoff : ℕ} [Fact p.Prime]
    {α G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (F : RFactor G)
    (hcutoff :
      cutoff ≤ u.weight wt * p ^ a + v.weight wt * p ^ b)
    (hc : F.multiplicity ≠ 0)
    (hgood : F.Good p a b) :
    ∃ E : WCFactor p f wt cutoff,
      E.eval = F.eval (u.eval f) (v.eval f) ∧
        E.multiplicity =
          F.multiplicity /
            ((p ^ padicValNat p F.multiplicity.natAbs : ℕ) : ℤ) := by
  let e : ℕ := padicValNat p F.multiplicity.natAbs
  have hcAbs : F.multiplicity.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr hc
  have hdivNat : p ^ e ∣ F.multiplicity.natAbs :=
    (padicValNat_dvd_iff_le hcAbs).2 le_rfl
  have hdiv : ((p ^ e : ℕ) : ℤ) ∣ F.multiplicity :=
    Int.natCast_dvd.mpr hdivNat
  let E : WCFactor p f wt cutoff :=
    { word := CWord.hallPairBind u v F.word
      primeExponent := e
      multiplicity := F.multiplicity / ((p ^ e : ℕ) : ℤ)
      conjugator := F.conjugator
      weight_bound :=
        HPGood.leweighthall_paibinmulpri_powpadicvalnat
          wt u v hcutoff hc hgood }
  refine ⟨E, ?_, rfl⟩
  have hmul :
      ((p ^ e : ℕ) : ℤ) *
          (F.multiplicity / ((p ^ e : ℕ) : ℤ)) =
        F.multiplicity := by
    rw [mul_comm, Int.ediv_mul_cancel hdiv]
  simp only [E, WCFactor.eval, RFactor.eval]
  rw [CWord.eval_pair_bind]
  rw [← zpow_natCast, ← zpow_mul, hmul]

/-- A good raw Hall factor becomes a list of at most one admitted weighted
factor; the empty list handles a zero coefficient. -/
lemma weighted_factor_good
    {p a b cutoff : ℕ} [Fact p.Prime]
    {α G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (F : RFactor G)
    (hcutoff :
      cutoff ≤ u.weight wt * p ^ a + v.weight wt * p ^ b)
    (hgood : F.Good p a b) :
    ∃ L : List (WCFactor p f wt cutoff),
      L.length ≤ 1 ∧
        WCFactor.listEval L =
          F.eval (u.eval f) (v.eval f) := by
  by_cases hc : F.multiplicity = 0
  · refine ⟨[], by simp, ?_⟩
    simp [RFactor.eval, hc]
  · obtain ⟨E, hE, _hEmult⟩ :=
      weighted_good_ne
        u v F hcutoff hc hgood
    exact ⟨[E], by simp, by simpa using hE⟩

/-- Substitution turns an ordered list of good raw Hall factors into no more
admitted weighted factors than the original raw-factor count. -/
lemma list_weighted_good
    {p a b cutoff : ℕ} [Fact p.Prime]
    {α G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (hcutoff :
      cutoff ≤ u.weight wt * p ^ a + v.weight wt * p ^ b) :
    ∀ L : List (RFactor G),
      (∀ F ∈ L, F.Good p a b) →
        ∃ M : List (WCFactor p f wt cutoff),
          M.length ≤ L.length ∧
            WCFactor.listEval M =
              PPColl.listEval (u.eval f) (v.eval f) L
  | [], _ => ⟨[], by simp⟩
  | F :: L, hgood => by
      obtain ⟨MF, hMFlen, hMFeval⟩ :=
        weighted_factor_good
          u v F hcutoff (hgood F (by simp))
      obtain ⟨ML, hMLlen, hMLeval⟩ :=
        list_weighted_good
          u v hcutoff L (by
            intro E hE
            exact hgood E (by simp [hE]))
      refine ⟨MF ++ ML, ?_, ?_⟩
      · simpa only [List.length_append, List.length_cons, Nat.add_comm] using
          Nat.add_le_add hMFlen hMLlen
      · rw [WCFactor.listEval_append,
          PPColl.listEval_cons, hMFeval, hMLeval]

/-- Number of normalized schedule values contributed by one raw Hall
coefficient after its maximal certified `p`-power has been extracted. -/
def normalizedZassenhausCost
    (p : ℕ)
    {G : Type*} [Group G]
    (F : RFactor G) :
    ℕ :=
  (F.multiplicity /
      ((p ^ padicValNat p F.multiplicity.natAbs : ℕ) : ℤ)).natAbs

/-- Total normalized schedule cost of an ordered raw Hall-factor list. -/
def listNormalizedCost
    (p : ℕ)
    {G : Type*} [Group G]
    (L : List (RFactor G)) :
    ℕ :=
  (L.map (normalizedZassenhausCost p)).sum

@[simp]
lemma normalized_zassenhaus_cost
    (p : ℕ)
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (F : RFactor G) :
    normalizedZassenhausCost p (F.mapHom φ) =
      normalizedZassenhausCost p F :=
  rfl

@[simp]
lemma normalized_cost_hom
    (p : ℕ)
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H)
    (L : List (RFactor G)) :
    listNormalizedCost p (listMapHom φ L) =
      listNormalizedCost p L := by
  induction L with
  | nil =>
      rfl
  | cons F L ih =>
      change
        normalizedZassenhausCost p (F.mapHom φ) +
            listNormalizedCost p (listMapHom φ L) =
          normalizedZassenhausCost p F +
            listNormalizedCost p L
      rw [normalized_zassenhaus_cost, ih]

/-- One good raw Hall factor expands directly to normalized Zassenhaus
schedule values, bounded by its residual coefficient cost. -/
lemma scheduled_raw_good
    {p d n a b : ℕ} [Fact p.Prime]
    {α G : Type*} [Group G]
    (hn : 0 < n)
    (f : α → G)
    (u v : CWord α)
    (F : RFactor G)
    (hcutoff :
      n ≤ u.weight (fun _ => 1) * p ^ a +
        v.weight (fun _ => 1) * p ^ b)
    (hgood : F.Good p a b) :
    ∃ L : List (BSValue p d n G),
      (L.map BSValue.eval).prod =
          F.eval (u.eval f) (v.eval f) ∧
        L.length ≤ normalizedZassenhausCost p F := by
  by_cases hc : F.multiplicity = 0
  · refine ⟨[], ?_, ?_⟩
    · simp [RFactor.eval, hc]
    · simp [normalizedZassenhausCost, hc]
  · obtain ⟨E, hEeval, hEmult⟩ :=
      weighted_good_ne
        u v F hcutoff hc hgood
    obtain ⟨L, hLeval, hLlen⟩ :=
      scheduled_weighted_length
        p d n hn f E
    refine ⟨L, hLeval.trans hEeval, ?_⟩
    rw [hLlen, hEmult]
    rfl

/-- An ordered good raw Hall-factor list expands directly to normalized
Zassenhaus schedule values, with the residual costs added in collection order. -/
lemma scheduled_value_good
    {p d n a b : ℕ} [Fact p.Prime]
    {α G : Type*} [Group G]
    (hn : 0 < n)
    (f : α → G)
    (u v : CWord α)
    (hcutoff :
      n ≤ u.weight (fun _ => 1) * p ^ a +
        v.weight (fun _ => 1) * p ^ b) :
    ∀ R : List (RFactor G),
      (∀ F ∈ R, F.Good p a b) →
        ∃ L : List (BSValue p d n G),
          (L.map BSValue.eval).prod =
              PPColl.listEval (u.eval f) (v.eval f) R ∧
            L.length ≤ listNormalizedCost p R
  | [], _ => ⟨[], by simp [listNormalizedCost]⟩
  | F :: R, hgood => by
      obtain ⟨LF, hLFeval, hLFlen⟩ :=
        scheduled_raw_good
          hn f u v F hcutoff (hgood F (by simp))
      obtain ⟨LR, hLReval, hLRlen⟩ :=
        scheduled_value_good
          hn f u v hcutoff R (by
            intro E hE
            exact hgood E (by simp [hE]))
      refine ⟨LF ++ LR, ?_, ?_⟩
      · rw [List.map_append, List.prod_append, hLFeval, hLReval,
          PPColl.listEval_cons]
      · simpa [listNormalizedCost] using
          Nat.add_le_add hLFlen hLRlen

end RFactor

namespace Trace

/-- A Hall-Petresco trace gives an explicit bounded list of admitted weighted
factors after substitution. -/
lemma list_weighted_eval
    {p a b cutoff : ℕ} [Fact p.Prime]
    {α G : Type*} [Group G]
    {f : α → G}
    {wt : α → ℕ}
    (u v : CWord α)
    (T : Trace p (u.eval f) (v.eval f) a b)
    (hcutoff :
      cutoff ≤ u.weight wt * p ^ a + v.weight wt * p ^ b) :
    ∃ M : List (WCFactor p f wt cutoff),
      M.length ≤ T.factors.length ∧
        WCFactor.listEval M =
          ⁅(u.eval f) ^ (p ^ a), (v.eval f) ^ (p ^ b)⁆ := by
  obtain ⟨M, hMlen, hMeval⟩ :=
    RFactor.list_weighted_good
      u v hcutoff T.factors T.factors_good
  exact ⟨M, hMlen, hMeval.trans T.eval_eq⟩

end Trace
end PPColl

/-- Every value of an arbitrary admissible scheme at positive depth is one
selected value of the concrete normalized schedule. -/
lemma bounded_scheduled_scheme
    {p d n : ℕ} [Fact p.Prime]
    (hn : 0 < n)
    {G : Type*} [Group G]
    (S : ZWScheme p n)
    (a : Fin S.arity → G) :
    ∃ z : BSValue p d n G,
      z.eval = S.eval a := by
  obtain ⟨i, b, hb⟩ :=
    bounded_slot_commutator
      p d n S.frobenius hn a S.word S.level_bound
  exact ⟨⟨i, b⟩, by
    simpa [BSValue.eval,
      ZWScheme.eval] using hb⟩

/-- Normalize every slot in an arbitrary finite schedule without changing its
ordered product or its width. -/
lemma bounded_scheduled_value
    {p d n : ℕ} [Fact p.Prime]
    (hn : 0 < n)
    {G : Type*} [Group G]
    (S : ZWSched p d n)
    (a : S.Arguments G) :
    ∃ L : List (BSValue p d n G),
      L.length = S.width ∧
        (L.map BSValue.eval).prod = S.eval a := by
  choose z hz using fun i =>
    bounded_scheduled_scheme
      (p := p) (d := d) hn (S.slot i) (a i)
  refine ⟨List.ofFn z, by simp, ?_⟩
  rw [List.map_ofFn, ZWSched.eval_def]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact hz i

/-- At positive depth, the requested finite collection structure is equivalent
to one quotient-independent bound on normalized list length. -/
theorem collection_nonempty_normalized
    (p d n : ℕ) [Fact p.Prime]
    (hn : 0 < n) :
    Nonempty (FSColl.{u} p d n) ↔
      ∃ k, BoundedNormalizedList.{u} p d n k := by
  constructor
  · rintro ⟨C⟩
    refine ⟨C.schedule.width, ?_⟩
    intro Q _ _ hQ t ht x hx
    obtain ⟨a, ha⟩ := C.factor Q hQ t ht x hx
    obtain ⟨L, hLlen, hLeval⟩ :=
      bounded_scheduled_value
        hn C.schedule a
    exact ⟨L, by simp [hLlen], hLeval.trans ha⟩
  · rintro ⟨k, hk⟩
    exact
      collection_normalized_list hk

/-- The undirected left Cayley graph attached to a set of group elements. -/
def leftCayleyGraph
    {G : Type*} [Group G]
    (S : Set G) :
    SimpleGraph G where
  Adj x y :=
    x ≠ y ∧
      ∃ s ∈ S, y = s * x ∨ x = s * y
  symm := by
    intro x y h
    rcases h with ⟨hxy, s, hs, hstep⟩
    exact ⟨hxy.symm, s, hs, hstep.elim Or.inr Or.inl⟩
  loopless := by
    exact ⟨fun x h => h.1 rfl⟩

/-- A product of Cayley generators can be reached from the identity in the
left Cayley graph. -/
lemma cayley_graph_reachable
    {G : Type*} [Group G]
    {S : Set G} :
    ∀ L : List G,
      (∀ z ∈ L, z ∈ S) →
        (leftCayleyGraph S).Reachable 1 L.prod
  | [], _ => SimpleGraph.Reachable.refl _
  | s :: L, hL => by
      have htail :=
        cayley_graph_reachable L (by
          intro z hz
          exact hL z (by simp [hz]))
      by_cases heq : s * L.prod = L.prod
      · simpa [heq] using htail
      · exact
          htail.trans
            ⟨SimpleGraph.Walk.cons
              ⟨fun h => heq h.symm, s, hL s (by simp), Or.inl rfl⟩
              SimpleGraph.Walk.nil⟩

/-- A walk in an inverse-closed Cayley graph records a product of generators
with exactly the same length. -/
lemma cayley_graph_walk
    {G : Type*} [Group G]
    {S : Set G}
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S) :
    ∀ {x y : G} (W : (leftCayleyGraph S).Walk x y),
      ∃ L : List G,
        (∀ z ∈ L, z ∈ S) ∧
          L.prod * x = y ∧
            L.length = W.length
  | _, _, .nil => ⟨[], by simp⟩
  | x, y, .cons h W => by
      obtain ⟨L, hLmem, hLprod, hLlen⟩ :=
        cayley_graph_walk hinv W
      rcases h with ⟨_hne, s, hs, hstep | hstep⟩
      · refine ⟨L ++ [s], ?_, ?_, ?_⟩
        · intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hLmem z hz
          · simp only [List.mem_singleton] at hz
            subst z
            exact hs
        · rw [List.prod_append]
          simp only [List.prod_singleton]
          rw [mul_assoc, ← hstep]
          exact hLprod
        · simp [hLlen]
      · refine ⟨L ++ [s⁻¹], ?_, ?_, ?_⟩
        · intro z hz
          rcases List.mem_append.mp hz with hz | hz
          · exact hLmem z hz
          · simp only [List.mem_singleton] at hz
            subst z
            exact hinv s hs
        · rw [List.prod_append]
          simp only [List.prod_singleton]
          simpa [hstep, mul_assoc] using hLprod
        · simp [hLlen]

/-- In a finite group, an element generated by an inverse-closed set is a
product of at most `Nat.card G` selected generators. -/
lemma list_closure_inv
    {G : Type*} [Group G] [Finite G]
    {S : Set G}
    (hinv : ∀ s ∈ S, s⁻¹ ∈ S)
    {x : G}
    (hx : x ∈ Subgroup.closure S) :
    ∃ L : List G,
      (∀ z ∈ L, z ∈ S) ∧
        L.prod = x ∧
          L.length ≤ Nat.card G := by
  letI : Fintype G := Fintype.ofFinite G
  have hxmon : x ∈ Submonoid.closure S := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hx
  obtain ⟨L, hLmem, hLprod⟩ :=
    Submonoid.exists_list_of_mem_closure hxmon
  have hreach : (leftCayleyGraph S).Reachable 1 x := by
    rw [← hLprod]
    exact cayley_graph_reachable L hLmem
  obtain ⟨P, hPpath⟩ := hreach.exists_isPath
  obtain ⟨M, hMmem, hMprod, hMlen⟩ :=
    cayley_graph_walk hinv P
  refine ⟨M, hMmem, ?_, ?_⟩
  · simpa using hMprod
  · rw [hMlen]
    simpa [Nat.card_eq_fintype_card] using hPpath.length_lt.le

/-- Lift a list whose entries lie in a function range to a list of preimages. -/
lemma list_forall_range
    {α β : Type*}
    (f : α → β) :
    ∀ L : List β,
      (∀ x ∈ L, x ∈ Set.range f) →
        ∃ M : List α,
          M.length = L.length ∧
            M.map f = L
  | [], _ => ⟨[], rfl, rfl⟩
  | x :: L, hL => by
      obtain ⟨a, rfl⟩ := hL x (by simp)
      obtain ⟨M, hMlen, hMmap⟩ :=
        list_forall_range f L (by
          intro y hy
          exact hL y (by simp [hy]))
      exact ⟨a :: M, by simp [hMlen], by simp [hMmap]⟩

/-- Every element of the normalized schedule subgroup in a finite group has a
normalized representative list no longer than the group cardinality. -/
lemma list_bounded_scheduled
    {p d n : ℕ} [Fact p.Prime]
    (hn : 0 < n)
    {G : Type*} [Group G] [Finite G]
    {x : G}
    (hx : x ∈ boundedScheduleSubgroup p d n G) :
    ∃ L : List (BSValue p d n G),
      L.length ≤ Nat.card G ∧
        (L.map BSValue.eval).prod = x := by
  classical
  rw [bounded_schedule_closure p d n hn G] at hx
  obtain ⟨M, hMmem, hMprod, hMlen⟩ :=
    list_closure_inv
      (fun _ hy => bounded_scheduled_inv hn hy) hx
  obtain ⟨L, hLlen, hLeval⟩ :=
    list_forall_range
      (BSValue.eval :
        BSValue p d n G → G)
      M (by
        intro y hy
        simpa [boundedScheduledSet] using hMmem y hy)
  refine ⟨L, ?_, ?_⟩
  · rw [hLlen]
    exact hMlen
  · rw [hLeval]
    exact hMprod

/-- The algebraic generation statement left to the Hall recollection argument:
the explicit Zassenhaus term is generated by normalized schedule values. -/
def NormalizedZassenhausGeneration
    (p d n : ℕ) [Fact p.Prime] :
    Prop :=
  ∀ (G : Type u) [Group G],
    zassenhausFiltration p G n ≤
      boundedScheduleSubgroup p d n G

/-- Every restricted `N`-series contains the lower-central series at the
expected one-based depth. -/
lemma lower_restricted_n
    {p : ℕ}
    {G : Type*} [Group G]
    (F : RNSeries p G) :
    ∀ i : ℕ,
      Subgroup.lowerCentralSeries G i ≤ F (i + 1)
  | 0 => by
      rw [Subgroup.lowerCentralSeries_zero, RNSeries.one_eq_top]
  | i + 1 => by
      rw [Subgroup.lowerCentralSeries_succ]
      exact
        (Subgroup.commutator_mono
            (lower_restricted_n F i)
            (by rw [RNSeries.one_eq_top])).trans
          (F.commutator_le (Nat.succ_ne_zero i) one_ne_zero)

/-- The explicit Zassenhaus filtration is contained in every restricted
`N`-series with the same prime parameter. -/
lemma restricted_n_series
    {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G]
    (F : RNSeries p G)
    (n : ℕ) :
    zassenhausFiltration p G n ≤ F n := by
  rw [zassenhausFiltration]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, e, x, hx, hlevel, rfl⟩
  exact
    RNSeries.HasDepth.pow_p_iteratele
      (F := F)
      (lower_restricted_n F i hx)
      hlevel

/-- The first normalized weighted-word term is the whole group. -/
lemma weighted_id_top
    (p : ℕ)
    (G : Type*) [Group G] :
    weightedCommutatorSubgroup
        p (fun z : G => z) (fun _ => 1) 1 =
      ⊤ := by
  apply top_unique
  intro x _hx
  exact
    Subgroup.subset_normalClosure
      ⟨.atom x, 0, by simp, by simp⟩

/-- Every `p`th power is already a normalized weighted-word generator at
depth two. -/
lemma p_weighted_id
    (p : ℕ) [Fact p.Prime]
    (G : Type*) [Group G] :
    pPowerSubgroup p G ≤
      weightedCommutatorSubgroup
        p (fun z : G => z) (fun _ => 1) 2 := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g, rfl⟩
  simpa using
    (CWord.evalpowprime_powermemweight_powcomworsub
      (p := p)
      (f := fun z : G => z)
      (wt := fun _ : G => 1)
      (cutoff := 2)
      (w := .atom g)
      (e := 1)
      (by simpa using (Fact.out : Nat.Prime p).two_le))

/-- Every ordinary commutator is already generated by normalized unit-weight
words at depth two. -/
lemma commutator_weighted_id
    (p : ℕ)
    (G : Type*) [Group G] :
    commutator G ≤
      weightedCommutatorSubgroup
        p (fun z : G => z) (fun _ => 1) 2 := by
  rw [← Subgroup.lowerCentralSeries_one]
  simpa using
    (lower_high_id G 1).trans
      (high_weighted_power
        p (fun z : G => z) (fun _ => 1) 2)

/-- Normalized Hall generation is unconditional at depth two for every
prime: `D₂ = G^p ⋁ [G,G]`, and both summands are normalized ranges. -/
lemma normalized_generation_two
    (p d : ℕ) [Fact p.Prime] :
    NormalizedZassenhausGeneration.{u} p d 2 := by
  intro G _instGroupG
  rw [filtration_p_frattini, modPFrattini,
    bounded_weighted_id p d 2 (by norm_num) G]
  exact sup_le
    (p_weighted_id p G)
    (commutator_weighted_id p G)

/-- A depth-two collection schedule uniformly factors the mod-`p` Frattini
subgroup, since the second Zassenhaus term is exactly that subgroup. -/
lemma FSColl.exists_modp_frattfactor
    {p d : ℕ} [Fact p.Prime]
    (C : FSColl.{u} p d 2)
    {Q : Type u} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q)
    (t : Fin d → Q)
    (ht : GeneratedBy t)
    {x : Q}
    (hx : x ∈ modPFrattini p Q) :
    ∃ f : Fin C.schedule.width → Q,
      (∀ i, f i ∈ (C.schedule.slot i).range Q) ∧
        (List.ofFn f).prod = x := by
  exact
    C.exists_factorization hQ t ht
      (by simpa [filtration_p_frattini] using hx)

end Submission
