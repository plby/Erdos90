import Towers.Algebra.CompletedGroupAlgebra.CoreBoundedWords


namespace Towers

universe u

/-!
Auxiliary monomials in the noncommuting variables `x i`, where
`x i` should morally be `s i - 1` in the augmentation quotient.
-/

def denseGeneratorsMonomial
    {d : ℕ} {R : Type u} [Monoid R]
    (x : Fin d → R) (l : List (Fin d)) : R :=
  (l.map x).prod

def denseShortMonomials
    {d : ℕ} {R : Type u} [Monoid R]
    (x : Fin d → R) (N : ℕ) : Set R :=
  { y | ∃ l : List (Fin d), l.length < N ∧ y = denseGeneratorsMonomial x l }

def shortMonomialSubmodule
    (p : ℕ)
    {d : ℕ} {R : Type u}
    [Ring R] [Algebra (ZMod p) R]
    (x : Fin d → R) (N : ℕ) : Submodule (ZMod p) R :=
  Submodule.span (ZMod p) (denseShortMonomials x N)

/-!
Finite-dimensionality/closedness of the short-word span.
-/

lemma dense_short_monomial
    {p : ℕ} [Fact p.Prime]
    {d : ℕ} {R : Type u} [Ring R] [Algebra (ZMod p) R]
    (x : Fin d → R) (N : ℕ) :
    Finite (shortMonomialSubmodule (p := p) x N) := by
  classical
  let ι : Type u := ULift.{u} (Σ k : Fin N, List.Vector (Fin d) k)
  haveI : Finite ι := by
    dsimp [ι]
    infer_instance
  let w : ι → R := fun a => denseGeneratorsMonomial x a.down.2.toList
  have hmonomials : denseShortMonomials x N = Set.range w := by
    ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨⟨⟨l.length, hl⟩, ⟨l, rfl⟩⟩⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.down.2.toList, by simp, rfl⟩
  have hfg : (shortMonomialSubmodule (p := p) x N).FG := by
    rw [shortMonomialSubmodule, hmonomials]
    exact Submodule.fg_span (Set.finite_range w)
  haveI : Module.Finite (ZMod p)
      (shortMonomialSubmodule (p := p) x N) :=
    Module.Finite.of_fg hfg
  haveI : Finite (ZMod p) := by
    haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
    infer_instance
  exact Module.finite_of_finite (ZMod p)

lemma short_monomial_top
    {p : ℕ} [Fact p.Prime]
    {d : ℕ} {R : Type u} [Ring R] [Algebra (ZMod p) R]
    (x : Fin d → R) {N : ℕ}
    (hspan : shortMonomialSubmodule (p := p) x N = ⊤) :
    Finite R := by
  let V := shortMonomialSubmodule (p := p) x N
  haveI : Finite V :=
    dense_short_monomial (p := p) x N
  exact
    Finite.of_injective
      (fun r : R => (⟨r, by
        change r ∈ shortMonomialSubmodule (p := p) x N
        rw [hspan]
        trivial⟩ : V))
      (by
        intro a b hab
        exact Subtype.ext_iff.mp hab)

lemma short_monomial_t
    {p : ℕ} [Fact p.Prime]
    {d : ℕ} {R : Type u}
    [Ring R] [TopologicalSpace R] [T1Space R] [Algebra (ZMod p) R]
    (x : Fin d → R) (N : ℕ) :
    IsClosed ((shortMonomialSubmodule (p := p) x N : Set R)) := by
  classical
  haveI : Finite (shortMonomialSubmodule (p := p) x N) :=
    dense_short_monomial (p := p) x N
  haveI : Fintype (shortMonomialSubmodule (p := p) x N) :=
    Fintype.ofFinite (shortMonomialSubmodule (p := p) x N)
  exact
    (Set.toFinite
      (shortMonomialSubmodule (p := p) x N : Set R)).isClosed

/-!
Algebraic closure properties of the short-word span.
-/

lemma generators_short_submodule
    {p : ℕ}
    {d : ℕ} {R : Type u} [Ring R] [Algebra (ZMod p) R]
    (x : Fin d → R) {N : ℕ}
    (hN : 0 < N) :
    (1 : R) ∈ shortMonomialSubmodule (p := p) x N := by
  exact Submodule.subset_span ⟨[], hN, by simp [denseGeneratorsMonomial]⟩

lemma short_monomial_long
    {p : ℕ}
    {d : ℕ} {R : Type u} [Ring R] [Algebra (ZMod p) R]
    (x : Fin d → R) {N : ℕ}
    (hzero :
      ∀ l : List (Fin d), N ≤ l.length → denseGeneratorsMonomial x l = 0) :
    ∀ {a b : R},
      a ∈ shortMonomialSubmodule (p := p) x N →
      b ∈ shortMonomialSubmodule (p := p) x N →
      a * b ∈ shortMonomialSubmodule (p := p) x N := by
  intro a b ha hb
  let V := shortMonomialSubmodule (p := p) x N
  change a * b ∈ V
  change a ∈ V at ha
  change b ∈ V at hb
  refine Submodule.span_induction
    (p := fun a _ => ∀ {b : R}, b ∈ V → a * b ∈ V)
    ?left_generator ?left_zero ?left_add ?left_smul ha hb
  · intro a ha b hb
    rcases ha with ⟨la, hla, rfl⟩
    refine Submodule.span_induction
      (p := fun b _ => denseGeneratorsMonomial x la * b ∈ V)
      ?right_generator ?right_zero ?right_add ?right_smul hb
    · intro b hb
      rcases hb with ⟨lb, hlb, rfl⟩
      by_cases hlength : (la ++ lb).length < N
      · exact
          Submodule.subset_span
            ⟨la ++ lb, hlength, by
              simp [denseGeneratorsMonomial, List.map_append, List.prod_append]⟩
      · have hzero' : denseGeneratorsMonomial x (la ++ lb) = 0 :=
          hzero (la ++ lb) (Nat.le_of_not_gt hlength)
        rw [← show
          denseGeneratorsMonomial x (la ++ lb) =
            denseGeneratorsMonomial x la * denseGeneratorsMonomial x lb by
              simp [denseGeneratorsMonomial, List.map_append, List.prod_append]]
        rw [hzero']
        exact V.zero_mem
    · simp only [mul_zero]
      exact V.zero_mem
    · intro b c _hb _hc hb_mem hc_mem
      rw [mul_add]
      exact V.add_mem hb_mem hc_mem
    · intro c b _hb hb_mem
      rw [Algebra.mul_smul_comm]
      exact V.smul_mem c hb_mem
  · intro b _hb
    rw [zero_mul]
    exact V.zero_mem
  · intro a b _ha _hb ha_mem hb_mem c hc
    rw [add_mul]
    exact V.add_mem (ha_mem hc) (hb_mem hc)
  · intro c a _ha ha_mem b hb
    rw [Algebra.smul_mul_assoc]
    exact V.smul_mem c (ha_mem hb)

lemma generator_monomial_submodule
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {R : Type u} [Ring R] [Algebra (ZMod p) R]
    (φ : Γ →* Units R)
    (x : Fin d → R) {N : ℕ}
    (hN : 0 < N)
    (hzero :
      ∀ l : List (Fin d), N ≤ l.length → denseGeneratorsMonomial x l = 0)
    (hx :
      ∀ i : Fin d, ((φ (s i) : Units R) : R) = 1 + x i) :
    ∀ i : Fin d,
      ((φ (s i) : Units R) : R) ∈
        shortMonomialSubmodule (p := p) x N := by
  intro i
  rw [hx i]
  apply
    (shortMonomialSubmodule (p := p) x N).add_mem
      (generators_short_submodule (p := p) x hN)
  by_cases hi : 1 < N
  · exact
      Submodule.subset_span
        ⟨[i], hi, by simp [denseGeneratorsMonomial]⟩
  · have hxi : x i = 0 := by
      simpa [denseGeneratorsMonomial] using
        hzero [i] (Nat.le_of_not_gt hi)
    rw [hxi]
    exact (shortMonomialSubmodule (p := p) x N).zero_mem

lemma inv_monomial_submodule
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {R : Type u} [Ring R] [Algebra (ZMod p) R]
    (φ : Γ →* Units R)
    (x : Fin d → R) {N : ℕ}
    (hN : 0 < N)
    (hzero :
      ∀ l : List (Fin d), N ≤ l.length → denseGeneratorsMonomial x l = 0)
    (hx :
      ∀ i : Fin d, ((φ (s i) : Units R) : R) = 1 + x i) :
    ∀ i : Fin d,
      (((φ (s i))⁻¹ : Units R) : R) ∈
        shortMonomialSubmodule (p := p) x N := by
  intro i
  let V := shortMonomialSubmodule (p := p) x N
  have hone : (1 : R) ∈ V :=
    generators_short_submodule (p := p) x hN
  have hmul : ∀ {a b : R}, a ∈ V → b ∈ V → a * b ∈ V :=
    short_monomial_long
      (p := p) x hzero
  have hxi : x i ∈ V := by
    by_cases hi : 1 < N
    · exact
        Submodule.subset_span
          ⟨[i], hi, by simp [denseGeneratorsMonomial]⟩
    · have hxi_zero : x i = 0 := by
        simpa [denseGeneratorsMonomial] using
          hzero [i] (Nat.le_of_not_gt hi)
      rw [hxi_zero]
      exact V.zero_mem
  have hpow_mem : ∀ k : ℕ, (-x i) ^ k ∈ V := by
    intro k
    induction k with
    | zero =>
        simpa using hone
    | succ k ih =>
        rw [pow_succ']
        exact hmul (V.neg_mem hxi) ih
  have hsum_mem : ∑ k ∈ Finset.range N, (-x i) ^ k ∈ V :=
    V.sum_mem fun k _hk => hpow_mem k
  have hpow_zero : x i ^ N = 0 := by
    simpa [denseGeneratorsMonomial] using
      hzero (List.replicate N i) (by simp)
  have hneg_pow_zero : (-x i) ^ N = 0 := by
    rw [neg_pow, hpow_zero, mul_zero]
  have hgeom :
      (1 + x i) * ∑ k ∈ Finset.range N, (-x i) ^ k = 1 := by
    simpa [hneg_pow_zero] using mul_neg_geom_sum (-x i) N
  have hinv :
      (((φ (s i))⁻¹ : Units R) : R) =
        ∑ k ∈ Finset.range N, (-x i) ^ k := by
    calc
      (((φ (s i))⁻¹ : Units R) : R) =
          (((φ (s i))⁻¹ : Units R) : R) * 1 := by simp
      _ = (((φ (s i))⁻¹ : Units R) : R) *
          ((1 + x i) * ∑ k ∈ Finset.range N, (-x i) ^ k) := by rw [hgeom]
      _ = ∑ k ∈ Finset.range N, (-x i) ^ k := by
        rw [← mul_assoc, ← hx i]
        simp
  rw [hinv]
  exact hsum_mem

/-!
If the generators and their inverses land in a multiplicatively closed submodule,
then every element of the abstract subgroup generated by them lands there.
-/

lemma closure_images_generators
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {d : ℕ} {s : Fin d → Γ}
    {R : Type u} [Ring R] [Algebra (ZMod p) R]
    (φ : Γ →* Units R)
    {V : Submodule (ZMod p) R}
    (hV_one : (1 : R) ∈ V)
    (hV_mul : ∀ {a b : R}, a ∈ V → b ∈ V → a * b ∈ V)
    (hgen : ∀ i : Fin d, ((φ (s i) : Units R) : R) ∈ V)
    (hgen_inv : ∀ i : Fin d, (((φ (s i))⁻¹ : Units R) : R) ∈ V) :
    ∀ γ ∈ Subgroup.closure (Set.range s),
      ((φ γ : Units R) : R) ∈ V ∧
        (((φ γ)⁻¹ : Units R) : R) ∈ V := by
  intro γ hγ
  refine Subgroup.closure_induction (k := Set.range s) ?mem ?one ?mul ?inv hγ
  · intro γ hγ
    rcases hγ with ⟨i, rfl⟩
    exact ⟨hgen i, hgen_inv i⟩
  · simpa using And.intro hV_one hV_one
  · intro a b _ha _hb ha hb
    constructor
    · simpa using hV_mul ha.1 hb.1
    · simpa using hV_mul hb.2 ha.2
  · intro a _ha ha
    simpa using And.intro ha.2 ha.1

/-!
Topological density of the chosen generators upgrades membership on the abstract
subgroup to membership on all of `Γ`.
-/

lemma images_dense_closure
    {p : ℕ}
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} {s : Fin d → Γ}
    {R : Type u} [Ring R] [TopologicalSpace R] [Algebra (ZMod p) R]
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (φ : Γ →* Units R)
    {V : Submodule (ZMod p) R}
    (hφ : Continuous fun γ : Γ => ((φ γ : Units R) : R))
    (hV_closed : IsClosed ((V : Set R)))
    (hV_on_closure :
      ∀ γ ∈ Subgroup.closure (Set.range s),
        ((φ γ : Units R) : R) ∈ V) :
    ∀ γ : Γ, ((φ γ : Units R) : R) ∈ V := by
  intro γ
  let f : Γ → R := fun g => ((φ g : Units R) : R)
  have hclosed_preimage : IsClosed (f ⁻¹' (V : Set R)) :=
    hV_closed.preimage hφ
  have hdense :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) =
        Set.univ := by
    simpa [Subgroup.topologicalClosure_coe] using
      congrArg (fun H : Subgroup Γ => (H : Set Γ)) hs
  have hsubset :
      ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹' (V : Set R) := by
    intro g hg
    exact hV_on_closure g hg
  have hclosure_subset :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹' (V : Set R) :=
    closure_minimal hsubset hclosed_preimage
  have hγ :
      γ ∈ closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) := by
    rw [hdense]
    exact Set.mem_univ γ
  exact hclosure_subset hγ

/-!
If the linear span of the group-like elements is dense, and a closed submodule
contains all group-like elements, then that submodule is everything.
-/

lemma short_monomial_submodule
    {p : ℕ}
    {Γ : Type u} [Group Γ]
    {d : ℕ}
    {R : Type u} [Ring R] [TopologicalSpace R] [Algebra (ZMod p) R]
    (φ : Γ →* Units R)
    (x : Fin d → R) {N : ℕ}
    (hspan_dense :
      Dense
        ((Submodule.span (ZMod p)
          (Set.range (fun γ : Γ => ((φ γ : Units R) : R))) : Set R)))
    (hV_closed :
      IsClosed ((shortMonomialSubmodule (p := p) x N : Set R)))
    (himages_mem :
      ∀ γ : Γ,
        ((φ γ : Units R) : R) ∈
          shortMonomialSubmodule (p := p) x N) :
    shortMonomialSubmodule (p := p) x N = ⊤ := by
  let V := shortMonomialSubmodule (p := p) x N
  let S : Set R := Set.range (fun γ : Γ => ((φ γ : Units R) : R))
  have hspan_le : Submodule.span (ZMod p) S ≤ V := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨γ, rfl⟩
    exact himages_mem γ
  have hclosure_le : closure ((Submodule.span (ZMod p) S : Set R)) ⊆ (V : Set R) :=
    closure_minimal hspan_le hV_closed
  apply top_unique
  intro y _hy
  exact hclosure_le (hspan_dense y)

/-!
Main abstract finiteness lemma.

This is the formal version of the argument:
short words span a finite-dimensional space `V`;
`V` is closed and multiplicatively stable;
the dense generators force all group elements into `V`;
the dense span of group elements forces `V = R`;
therefore `R` is finite.
-/

lemma dense_generator_augmentation
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {d : ℕ} {s : Fin d → Γ}
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {R : Type u}
    [Ring R] [TopologicalSpace R] [T1Space R] [Algebra (ZMod p) R]
    (φ : Γ →* Units R)
    (x : Fin d → R) {N : ℕ}
    (hN : 0 < N)
    (hφ : Continuous fun γ : Γ => ((φ γ : Units R) : R))
    (hspan_dense :
      Dense
        ((Submodule.span (ZMod p)
          (Set.range (fun γ : Γ => ((φ γ : Units R) : R))) : Set R)))
    (hx :
      ∀ i : Fin d, ((φ (s i) : Units R) : R) = 1 + x i)
    (hzero :
      ∀ l : List (Fin d), N ≤ l.length → denseGeneratorsMonomial x l = 0) :
    Finite R := by
  let V := shortMonomialSubmodule (p := p) x N
  have hV_closed : IsClosed (V : Set R) :=
    short_monomial_t (p := p) x N
  have hV_one : (1 : R) ∈ V :=
    generators_short_submodule (p := p) x hN
  have hV_mul : ∀ {a b : R}, a ∈ V → b ∈ V → a * b ∈ V :=
    short_monomial_long
      (p := p) x hzero
  have hgen : ∀ i : Fin d, ((φ (s i) : Units R) : R) ∈ V :=
    generator_monomial_submodule
      (p := p) φ x hN hzero hx
  have hgen_inv : ∀ i : Fin d, (((φ (s i))⁻¹ : Units R) : R) ∈ V :=
    inv_monomial_submodule
      (p := p) φ x hN hzero hx
  have hclosure :
      ∀ γ ∈ Subgroup.closure (Set.range s),
        ((φ γ : Units R) : R) ∈ V :=
    fun γ hγ =>
      (closure_images_generators
        (p := p) φ hV_one hV_mul hgen hgen_inv γ hγ).1
  have himages : ∀ γ : Γ, ((φ γ : Units R) : R) ∈ V :=
    images_dense_closure
      (p := p) hs φ hφ hV_closed hclosure
  have htop : V = ⊤ :=
    short_monomial_submodule
      (p := p) φ x hspan_dense hV_closed himages
  exact short_monomial_top (p := p) x htop

/-!
Discrete topology lemmas for finite quotients.
-/

lemma topology_t_1
    {α : Type u} [TopologicalSpace α] [T1Space α] [Finite α] :
    DiscreteTopology α := by
  infer_instance

lemma discrete_topology_units
    {M : Type u} [Group M]
    {R : Type u} [Monoid R] [TopologicalSpace R] [DiscreteTopology R]
    (φ : M →* Units R) :
    DiscreteTopology φ.range := by
  infer_instance

lemma discrete_topology_t
    {M : Type u} [Group M]
    {R : Type u} [Monoid R] [TopologicalSpace R] [T1Space R] [Finite R]
    (φ : M →* Units R) :
    DiscreteTopology φ.range := by
  letI : DiscreteTopology R :=
    topology_t_1
  exact discrete_topology_units φ

/-!
A package representing the intended quotient
`𝔽_p[[Γ]] / I^(n+1)`.

The point is that this package records the properties one actually proves
about the completed group algebra quotient, and then converts them into your
`DCCore`.
-/

structure DCData
    (p : ℕ) [Fact p.Prime]
    (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) : Type (u + 1) where
  core : DCCore (p := p) (Γ := Γ) s hs n
  quotient : Type u
  [instRing : Ring quotient]
  [instTopologicalSpace : TopologicalSpace quotient]
  [t1Space : T1Space quotient]
  [t2Space : T2Space quotient]
  [topologicalRing : IsTopologicalRing quotient]
  [instAlgebra : Algebra (ZMod p) quotient]
  unitMap : Γ →* Units quotient
  unitMap_continuous :
    Continuous fun γ : Γ => ((unitMap γ : Units quotient) : quotient)
  augmentationGenerators : Fin d → quotient
  generator_one_add :
    ∀ i : Fin d,
      ((unitMap (s i) : Units quotient) : quotient) =
        1 + augmentationGenerators i
  long_monomials_zero :
    ∀ l : List (Fin d), n + 1 ≤ l.length →
      denseGeneratorsMonomial augmentationGenerators l = 0
  images_dense_span :
    Dense
      ((Submodule.span (ZMod p)
        (Set.range (fun γ : Γ => ((unitMap γ : Units quotient) : quotient))) :
          Set quotient))
  jenningsLazardIdentification :
    Nonempty (DenseLazardIdentification core)
  core_augmentation_finite :
    Finite core.augmentationQuotient
  core_range_discrete :
    (letI := core.quotientTopology
     DiscreteTopology core.quotientUnitMap.range)

attribute [instance]
  DCData.instRing
  DCData.instTopologicalSpace
  DCData.t1Space
  DCData.t2Space
  DCData.topologicalRing
  DCData.instAlgebra

namespace DCData

noncomputable def toCore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : DCData
      (p := p) (Γ := Γ) s hs n) :
    DCCore (p := p) (Γ := Γ) s hs n :=
  A.core

lemma finite_quotient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : DCData
      (p := p) (Γ := Γ) s hs n) :
    Finite A.quotient := by
  exact
    dense_generator_augmentation
      (p := p) hs A.unitMap A.augmentationGenerators
      (Nat.succ_pos n) A.unitMap_continuous A.images_dense_span
      A.generator_one_add A.long_monomials_zero

lemma discreteTopology_quotient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : DCData
      (p := p) (Γ := Γ) s hs n) :
    DiscreteTopology A.quotient := by
  letI : Finite A.quotient := A.finite_quotient
  exact topology_t_1

lemma core_augmentation_quotient
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : DCData
      (p := p) (Γ := Γ) s hs n) :
    Finite (A.toCore).augmentationQuotient := by
  exact A.core_augmentation_finite

lemma discrete_topology_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : DCData
      (p := p) (Γ := Γ) s hs n) :
    (let C := A.toCore
     letI := C.quotientTopology
     DiscreteTopology C.quotientUnitMap.range) := by
  exact A.core_range_discrete

lemma jennings_identification_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : DCData
      (p := p) (Γ := Γ) s hs n) :
    Nonempty (DenseLazardIdentification A.toCore) := by
  exact A.jenningsLazardIdentification

end DCData

/-!
Reduction from the intended quotient package to your original existential theorem.
-/

lemma completed_core_data
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (A : DCData
      (p := p) (Γ := Γ) s hs n) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite C.augmentationQuotient ∧
        (letI := C.quotientTopology
         DiscreteTopology C.quotientUnitMap.range) ∧
        Nonempty (DenseLazardIdentification C) := by
  exact
    ⟨A.toCore, A.core_augmentation_quotient,
      A.discrete_topology_core, A.jennings_identification_core⟩

lemma completed_core_nonempty
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (hA :
      Nonempty
        (DCData
          (p := p) (Γ := Γ) s hs n)) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite C.augmentationQuotient ∧
        (letI := C.quotientTopology
         DiscreteTopology C.quotientUnitMap.range) ∧
        Nonempty (DenseLazardIdentification C) := by
  rcases hA with ⟨A⟩
  exact completed_core_data A

/-!
The unconditional constructor intentionally stops here. For Golod-Shafarevich,
construct quotient data from continuous finite p-group quotients and the pro-p
inverse limit, rather than from automatic continuity of arbitrary finite-index
subgroups.
-/

end Towers
