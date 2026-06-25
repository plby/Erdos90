import Towers.Group.InverseLimit

namespace Towers
namespace Topology

universe u v w
open Towers.Group

/-- A lightweight topology record, avoiding commitment to mathlib's topology API at this stage. -/
structure bTopo (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_empty : IsOpen ∅
  isOpen_inter : ∀ {U V}, IsOpen U → IsOpen V → IsOpen (U ∩ V)
  sUnion_open : ∀ S : Set (Set X), (∀ U ∈ S, IsOpen U) → IsOpen (⋃₀ S)


/-- The discrete lightweight topology, in which every subset is open. -/
def bTopo.discrete (X : Type u) : bTopo X where
  IsOpen := fun _ => True
  isOpen_univ := trivial
  isOpen_empty := trivial
  isOpen_inter := by intro U V hU hV; trivial
  sUnion_open := by intro S hS; trivial

@[simp] theorem bTopo.discrete_isOpen {X : Type u} (U : Set X) :
    (bTopo.discrete X).IsOpen U := trivial

/-- The whole space is open in a lightweight topology. -/
theorem bTopo.isOpen_univ' {X : Type u} (T : bTopo X) :
    T.IsOpen Set.univ :=
  T.isOpen_univ

/-- The empty set is open in a lightweight topology. -/
theorem bTopo.isOpen_empty' {X : Type u} (T : bTopo X) :
    T.IsOpen (∅ : Set X) :=
  T.isOpen_empty


/-- Binary unions are open in a lightweight topology. -/
theorem bTopo.isOpen_union {X : Type u} (T : bTopo X)
    {U V : Set X} (hU : T.IsOpen U) (hV : T.IsOpen V) : T.IsOpen (U ∪ V) := by
  have h := T.sUnion_open ({U, V} : Set (Set X)) (by
    intro W hW
    rcases hW with rfl | hW
    · exact hU
    · rcases hW with rfl
      exact hV)
  simpa [Set.sUnion_pair] using h


/-- Indexed unions are open in a lightweight topology. -/
theorem bTopo.iUnion_open {X : Type u} {ι : Type v} (T : bTopo X)
    (U : ι → Set X) (hU : ∀ i, T.IsOpen (U i)) :
    T.IsOpen (⋃ i, U i) := by
  have h := T.sUnion_open (Set.range U) (by
    intro W hW
    rcases hW with ⟨i, rfl⟩
    exact hU i)
  simpa [Set.sUnion_range] using h

/-- A finite intersection of two opens, named in binary form. -/
theorem bTopo.isOpen_inter' {X : Type u} (T : bTopo X)
    {U V : Set X} (hU : T.IsOpen U) (hV : T.IsOpen V) :
    T.IsOpen (U ∩ V) := T.isOpen_inter hU hV

/-- Density for the lightweight topology: every nonempty open set meets `S`. -/
def bDense {X : Type u} (T : bTopo X) (S : Set X) : Prop :=
  ∀ U : Set X, T.IsOpen U → U.Nonempty → (U ∩ S).Nonempty

/-- Density is monotone under enlarging the dense subset. -/
theorem bDense.mono {X : Type u} {T : bTopo X} {S U : Set X}
    (hS : bDense T S) (hsub : S ⊆ U) : bDense T U := by
  intro O hO hnon
  rcases hS O hO hnon with ⟨x, hxO, hxS⟩
  exact ⟨x, hxO, hsub hxS⟩

/-- A dense set meets every nonempty open set, named pointwise. -/
theorem bDense.exists_mem {X : Type u} {T : bTopo X} {S O : Set X}
    (hS : bDense T S) (hO : T.IsOpen O) (hne : O.Nonempty) :
    ∃ x, x ∈ O ∧ x ∈ S := by
  rcases hS O hO hne with ⟨x, hxO, hxS⟩
  exact ⟨x, hxO, hxS⟩

/-- Continuity with respect to the lightweight topology records. -/
def basicContinuous {X : Type u} {Y : Type v} (TX : bTopo X) (TY : bTopo Y)
    (f : X → Y) : Prop :=
  ∀ U : Set Y, TY.IsOpen U → TX.IsOpen {x | f x ∈ U}

/-- Openness with respect to the lightweight topology records. -/
def basicOpenMap {X : Type u} {Y : Type v} (TX : bTopo X) (TY : bTopo Y)
    (f : X → Y) : Prop :=
  ∀ U : Set X, TX.IsOpen U → TY.IsOpen (f '' U)

/-- Maps out of a discrete lightweight topology are continuous exactly when no condition
is imposed on preimages of opens. This named lemma is often convenient for finite targets. -/
theorem bTopo.continuous_from_discrete {X : Type u} {Y : Type v}
    (TY : bTopo Y) (f : X → Y) :
    basicContinuous (bTopo.discrete X) TY f := by
  intro U hU
  trivial

/-- Every map into a discrete lightweight topology is open provided its domain opens are
sent to arbitrary subsets (which are open in the codomain). -/
theorem bTopo.open_to_discrete {X : Type u} {Y : Type v}
    (TX : bTopo X) (f : X → Y) :
    basicOpenMap TX (bTopo.discrete Y) f := by
  intro U hU
  trivial


/-- Identity maps are continuous for the lightweight topology. -/
theorem basicContinuous_id {X : Type u} (T : bTopo X) :
    basicContinuous T T id := by
  intro U hU
  simpa using hU

/-- Identity maps are open for the lightweight topology. -/
theorem basic_open_id {X : Type u} (T : bTopo X) :
    basicOpenMap T T id := by
  intro U hU
  simpa using hU

/-- Constant maps are continuous for lightweight topologies. -/
theorem basicContinuous_const {X : Type u} {Y : Type v}
    (TX : bTopo X) (TY : bTopo Y) (y : Y) :
    basicContinuous TX TY (fun _ : X => y) := by
  intro U hU
  by_cases hy : y ∈ U
  · have : {x : X | y ∈ U} = Set.univ := by
      ext x; simp [hy]
    simpa [this] using TX.isOpen_univ
  · have : {x : X | y ∈ U} = (∅ : Set X) := by
      ext x; simp [hy]
    simpa [this] using TX.isOpen_empty

/-- Composition of lightweight continuous maps. -/
theorem basicContinuous_comp {X : Type u} {Y : Type v} {Z : Type w}
    (TX : bTopo X) (TY : bTopo Y) (TZ : bTopo Z)
    {f : X → Y} {g : Y → Z}
    (hf : basicContinuous TX TY f) (hg : basicContinuous TY TZ g) :
    basicContinuous TX TZ (fun x => g (f x)) := by
  intro U hU
  exact hf {y | g y ∈ U} (hg U hU)

/-- Composition of lightweight open maps. -/
theorem basic_open_comp {X : Type u} {Y : Type v} {Z : Type w}
    (TX : bTopo X) (TY : bTopo Y) (TZ : bTopo Z)
    {f : X → Y} {g : Y → Z}
    (hf : basicOpenMap TX TY f) (hg : basicOpenMap TY TZ g) :
    basicOpenMap TX TZ (fun x => g (f x)) := by
  intro U hU
  simpa [Set.image_image] using hg (f '' U) (hf U hU)

/-- A lightweight profinite topology package on a group. -/
structure pTopo (G : Type u) [Group G] where
  topology : bTopo G
  compact : ∀ C : Set (Set G), (∀ U ∈ C, topology.IsOpen U) →
    (Set.univ : Set G) ⊆ ⋃₀ C →
    ∃ F : Finset (Set G), (∀ U ∈ F, U ∈ C) ∧ (Set.univ : Set G) ⊆ ⋃₀ (↑F : Set (Set G))
  t2 : ∀ x y : G, x ≠ y → ∃ U V : Set G, topology.IsOpen U ∧ topology.IsOpen V ∧
    x ∈ U ∧ y ∈ V ∧ Disjoint U V
  totallyDisconnected : ∀ x y : G, x ≠ y → ∃ U : Set G, topology.IsOpen U ∧
    topology.IsOpen Uᶜ ∧ x ∈ U ∧ y ∉ U
  /-- A profinite-style neighborhood basis at `1` by open normal finite quotients. -/
  openNormalBasis : ∀ U : Set G, topology.IsOpen U → (1 : G) ∈ U →
    ∃ N : nSubgro G, topology.IsOpen (N.carrier : Set G) ∧
      (N.carrier : Set G) ⊆ U ∧ Finite (quotientGroup N)
  /-- Continuity of left translations, expressed by open preimages. -/
  left_translate_continuous : ∀ g U, topology.IsOpen U →
    topology.IsOpen {x : G | g * x ∈ U}
  /-- Continuity of right translations. -/
  right_translate_continuous : ∀ g U, topology.IsOpen U →
    topology.IsOpen {x : G | x * g ∈ U}
  /-- Continuity of inversion. -/
  inv_continuous : ∀ U, topology.IsOpen U → topology.IsOpen {x : G | x⁻¹ ∈ U}
  /-- Joint continuity of multiplication, in neighborhood form for the lightweight topology. -/
  mul_continuous_at : ∀ a b (U : Set G), topology.IsOpen U → a * b ∈ U →
    ∃ V W : Set G, topology.IsOpen V ∧ topology.IsOpen W ∧ a ∈ V ∧ b ∈ W ∧
      ∀ x ∈ V, ∀ y ∈ W, x * y ∈ U



/-- The discrete topology on a finite group is profinite in the lightweight sense.  This
provides a canonical target topology for finite quotient packages. -/
noncomputable def pTopo.discreteOfFintype (G : Type u) [Group G] [Fintype G] :
    pTopo G where
  topology := bTopo.discrete G
  compact := by
    classical
    intro C hopen hcover
    have hex : ∀ x : G, ∃ U : Set G, U ∈ C ∧ x ∈ U := by
      intro x
      have hx : x ∈ (⋃₀ C : Set G) := hcover (by trivial)
      rcases hx with ⟨U, hUC, hxU⟩
      exact ⟨U, hUC, hxU⟩
    choose U hUC hxU using hex
    refine ⟨Finset.univ.image U, ?_, ?_⟩
    · intro V hV
      rcases Finset.mem_image.mp hV with ⟨x, _hx, rfl⟩
      exact hUC x
    · intro x hx
      refine ⟨U x, ?_, hxU x⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)
  t2 := by
    intro x y hxy
    refine ⟨{x}, {y}, trivial, trivial, by simp, by simp, ?_⟩
    rw [Set.disjoint_left]
    intro z hzx hzy
    have hxz : z = x := by simpa using hzx
    have hyz : z = y := by simpa using hzy
    exact hxy (hxz.symm.trans hyz)
  totallyDisconnected := by
    intro x y hxy
    refine ⟨{x}, trivial, trivial, by simp, ?_⟩
    intro hy
    simp at hy
    exact hxy hy.symm
  openNormalBasis := by
    intro U hU h1
    let N : nSubgro G := { carrier := ⊥, normal' := by infer_instance }
    refine ⟨N, trivial, ?_, ?_⟩
    · intro x hx
      have hx1 : x = 1 := by simpa using hx
      simpa [hx1] using h1
    · dsimp [quotientGroup]
      infer_instance
  left_translate_continuous := by intro g U hU; trivial
  right_translate_continuous := by intro g U hU; trivial
  inv_continuous := by intro U hU; trivial
  mul_continuous_at := by
    intro a b U hU hab
    refine ⟨{a}, {b}, trivial, trivial, by simp, by simp, ?_⟩
    intro x hx y hy
    simp at hx hy
    subst x; subst y
    simpa using hab


/-- Neighborhood form of joint multiplication continuity in a profinite topology. -/
theorem pTopo.mul_continuous_at' {G : Type u} [Group G]
    (T : pTopo G) {a b : G} {U : Set G}
    (hU : T.topology.IsOpen U) (hab : a * b ∈ U) :
    ∃ V W : Set G, T.topology.IsOpen V ∧ T.topology.IsOpen W ∧ a ∈ V ∧ b ∈ W ∧
      ∀ x ∈ V, ∀ y ∈ W, x * y ∈ U :=
  T.mul_continuous_at a b U hU hab

/-- Left translation is continuous in the lightweight profinite topology. -/
theorem pTopo.leftTranslation_continuous {G : Type u} [Group G]
    (T : pTopo G) (g : G) :
    basicContinuous T.topology T.topology (fun x : G => g * x) := by
  intro U hU
  exact T.left_translate_continuous g U hU

/-- Right translation is continuous in the lightweight profinite topology. -/
theorem pTopo.rightTranslation_continuous {G : Type u} [Group G]
    (T : pTopo G) (g : G) :
    basicContinuous T.topology T.topology (fun x : G => x * g) := by
  intro U hU
  exact T.right_translate_continuous g U hU

/-- Inversion is continuous in the lightweight profinite topology. -/
theorem pTopo.inversion_continuous {G : Type u} [Group G]
    (T : pTopo G) :
    basicContinuous T.topology T.topology (fun x : G => x⁻¹) := by
  intro U hU
  exact T.inv_continuous U hU

/-- In a lightweight profinite group, an open subgroup is also closed: its complement
is a union of open left cosets. -/
theorem pTopo.open_compl_opensubgroup {G : Type u} [Group G]
    (T : pTopo G) (H : Subgroup G)
    (hH : T.topology.IsOpen (H : Set G)) :
    T.topology.IsOpen ((H : Set G)ᶜ) := by
  let C : Set (Set G) := {V | ∃ g : G, g ∉ H ∧ V = {x : G | g⁻¹ * x ∈ H}}
  have hCopen : ∀ V ∈ C, T.topology.IsOpen V := by
    intro V hV
    rcases hV with ⟨g, hg, rfl⟩
    exact T.left_translate_continuous g⁻¹ (H : Set G) hH
  have hcompl : ((H : Set G)ᶜ) = ⋃₀ C := by
    ext x
    constructor
    · intro hx
      have hxH : x ∉ H := by simpa using hx
      refine ⟨{y : G | x⁻¹ * y ∈ H}, ?_, ?_⟩
      · exact ⟨x, hxH, rfl⟩
      · simp
    · intro hx
      rcases hx with ⟨V, hVC, hxV⟩
      rcases hVC with ⟨g, hgH, rfl⟩
      change x ∉ H
      intro hxH
      have hginv : g⁻¹ * x ∈ H := hxV
      have hg_from : g ∈ H := by
        -- `g = x * (g⁻¹ * x)⁻¹`, so membership follows from subgroup closure.
        have hprod : x * (g⁻¹ * x)⁻¹ ∈ H := H.mul_mem hxH (H.inv_mem hginv)
        convert hprod using 1
        group
      exact hgH hg_from
  rw [hcompl]
  exact T.topology.sUnion_open C hCopen

/-- Named form of the open-normal basis property at the identity. -/
theorem pTopo.exists_open_normalsubset {G : Type u} [Group G]
    (T : pTopo G) {U : Set G} (hU : T.topology.IsOpen U)
    (h1 : (1 : G) ∈ U) :
    ∃ N : nSubgro G, T.topology.IsOpen (N.carrier : Set G) ∧
      (N.carrier : Set G) ⊆ U ∧ Finite (quotientGroup N) :=
  T.openNormalBasis U hU h1

/-- Translate the identity open-normal basis to a neighborhood of an arbitrary point. -/
theorem pTopo.existsopen_normalright_cosetsubset {G : Type u} [Group G]
    (T : pTopo G) {U : Set G} {g : G}
    (hU : T.topology.IsOpen U) (hg : g ∈ U) :
    ∃ N : nSubgro G, T.topology.IsOpen (N.carrier : Set G) ∧
      (∀ n ∈ (N.carrier : Set G), g * n ∈ U) ∧ Finite (quotientGroup N) := by
  let V : Set G := {x : G | g * x ∈ U}
  have hV : T.topology.IsOpen V := T.left_translate_continuous g U hU
  have h1 : (1 : G) ∈ V := by
    dsimp [V]
    simpa using hg
  rcases T.openNormalBasis V hV h1 with ⟨N, hNo, hsub, hfin⟩
  refine ⟨N, hNo, ?_, hfin⟩
  intro n hn
  exact hsub hn

/-- Translate the identity basis on the other side as well. -/
theorem pTopo.existsopen_normalleft_cosetsubset {G : Type u} [Group G]
    (T : pTopo G) {U : Set G} {g : G}
    (hU : T.topology.IsOpen U) (hg : g ∈ U) :
    ∃ N : nSubgro G, T.topology.IsOpen (N.carrier : Set G) ∧
      (∀ n ∈ (N.carrier : Set G), n * g ∈ U) ∧ Finite (quotientGroup N) := by
  let V : Set G := {x : G | x * g ∈ U}
  have hV : T.topology.IsOpen V := T.right_translate_continuous g U hU
  have h1 : (1 : G) ∈ V := by
    dsimp [V]
    simpa using hg
  rcases T.openNormalBasis V hV h1 with ⟨N, hNo, hsub, hfin⟩
  refine ⟨N, hNo, ?_, hfin⟩
  intro n hn
  exact hsub hn

/-- Equivalently, every open neighborhood of `g` contains a right coset of an open
normal subgroup. -/
theorem pTopo.exists_right_cosetsubset {G : Type u} [Group G]
    (T : pTopo G) {U : Set G} {g : G}
    (hU : T.topology.IsOpen U) (hg : g ∈ U) :
    ∃ N : nSubgro G, T.topology.IsOpen (N.carrier : Set G) ∧
      ({x : G | ∃ n ∈ (N.carrier : Set G), x = g * n} ⊆ U) ∧
      Finite (quotientGroup N) := by
  rcases T.existsopen_normalright_cosetsubset hU hg with ⟨N, hNo, hmul, hfin⟩
  refine ⟨N, hNo, ?_, hfin⟩
  intro x hx
  rcases hx with ⟨n, hn, rfl⟩
  exact hmul n hn


/-- A profinite `p`-group: a group with a profinite topology and finite
`p`-group quotients in view. -/
structure pPGroups (p : ℕ) (G : Type u) [Group G] where
  prime : Nat.Prime p
  top : pTopo G
  finite_level : ℕ → fQuotie G
  level_pgroup : ∀ n, fPGroups p (quotientGroup (finite_level n).normal)
  /-- Levels are nested kernels, so they form an actual inverse system basis. -/
  level_refines : ∀ n, (finite_level (n + 1)).normal.carrier ≤ (finite_level n).normal.carrier
  /-- The finite `p`-quotients come from open kernels in the profinite topology. -/
  level_open : ∀ n, top.topology.IsOpen ((finite_level n).normal.carrier : Set G)
  /-- The displayed levels form a neighborhood basis at the identity. -/
  level_basis : ∀ U : Set G, top.topology.IsOpen U → (1 : G) ∈ U →
    ∃ n, ((finite_level n).normal.carrier : Set G) ⊆ U

/-- The prime attached to a profinite p-group. -/
theorem pPGroups.prime_p {p : ℕ} {G : Type u} [Group G]
    (P : pPGroups p G) : Nat.Prime p := P.prime

/-- A profinite `p`-group package supplies the usual prime fact for `p`. -/
@[reducible] def pPGroups.fact_prime {p : ℕ} {G : Type u} [Group G]
    (P : pPGroups p G) : Fact p.Prime :=
  ⟨P.prime⟩

/-- Successive displayed kernels are nested. -/
theorem pPGroups.level_refines_succ {p : ℕ} {G : Type u} [Group G]
    (P : pPGroups p G) (n : ℕ) :
    (P.finite_level (n + 1)).normal.carrier ≤ (P.finite_level n).normal.carrier :=
  P.level_refines n

/-- An open normal subgroup in the lightweight topology. -/
structure oNSubgro (G : Type u) [Group G] (T : pTopo G) where
  normal : nSubgro G
  isOpen' : T.topology.IsOpen (normal.carrier : Set G)
  finiteQuotient : Finite (quotientGroup normal)
  contains_one : (1 : G) ∈ normal.carrier := normal.carrier.one_mem

/-- Each displayed level of a profinite `p`-group is an open normal subgroup. -/
def pPGroups.openLevel {p : ℕ} {G : Type u} [Group G]
    (P : pPGroups p G) (n : ℕ) : oNSubgro G P.top where
  normal := (P.finite_level n).normal
  isOpen' := P.level_open n
  finiteQuotient := (P.finite_level n).finite'

@[simp] theorem pPGroups.openLevel_normal {p : ℕ} {G : Type u} [Group G]
    (P : pPGroups p G) (n : ℕ) :
    (P.openLevel n).normal = (P.finite_level n).normal := rfl

/-- The nth displayed quotient is a finite p-group. -/
theorem pPGroups.level_is_pgroup {p : ℕ} {G : Type u} [Group G]
    (P : pPGroups p G) (n : ℕ) :
    fPGroups p (quotientGroup (P.finite_level n).normal) :=
  P.level_pgroup n

/-- The nth open level is open, as an accessor. -/
theorem pPGroups.open_level_open {p : ℕ} {G : Type u} [Group G]
    (P : pPGroups p G) (n : ℕ) :
    P.top.topology.IsOpen (((P.openLevel n).normal.carrier) : Set G) :=
  (P.openLevel n).isOpen'

/-- The displayed levels form an open-normal basis at the identity, packaged as subgroups. -/
theorem pPGroups.exists_open_levelsubset {p : ℕ} {G : Type u} [Group G]
    (P : pPGroups p G) {U : Set G}
    (hU : P.top.topology.IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ n, ((P.openLevel n).normal.carrier : Set G) ⊆ U :=
  P.level_basis U hU h1


/-- Build an open-normal subgroup package from its three defining witnesses. -/
def oNSubgro.ofNormal {G : Type u} [Group G] {T : pTopo G}
    (N : nSubgro G) (hopen : T.topology.IsOpen (N.carrier : Set G))
    (hfin : Finite (quotientGroup N)) : oNSubgro G T where
  normal := N
  isOpen' := hopen
  finiteQuotient := hfin


/-- Intersection of two open normal subgroups (with finiteness supplied for the finer quotient). -/
def oNSubgro.inf {G : Type u} [Group G] {T : pTopo G}
    (N M : oNSubgro G T)
    (hfin : Finite (quotientGroup (N.normal.inf M.normal))) : oNSubgro G T where
  normal := N.normal.inf M.normal
  isOpen' := by
    change T.topology.IsOpen ((N.normal.carrier : Set G) ∩ (M.normal.carrier : Set G))
    exact T.topology.isOpen_inter N.isOpen' M.isOpen'
  finiteQuotient := hfin

/-- The quotient projection associated to an open normal subgroup. -/
def oNSubgro.projection {G : Type u} [Group G] {T : pTopo G}
    (N : oNSubgro G T) : G →* quotientGroup N.normal :=
  N.normal.projection

/-- The projection attached to an open normal subgroup is surjective. -/
theorem oNSubgro.projection_surjective {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) :
    Function.Surjective N.projection := N.normal.projection_surjective

/-- The kernel of the open-normal projection is the displayed subgroup. -/
theorem oNSubgro.kernel_projection {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) :
    MonoidHom.ker N.projection = N.normal.carrier := N.normal.ker_projection

/-- The displayed open-normal subgroup is open. -/
theorem oNSubgro.isOpen {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) :
    T.topology.IsOpen (N.normal.carrier : Set G) :=
  N.isOpen'

/-- The identity belongs to an open normal subgroup. -/
theorem oNSubgro.one_mem {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) :
    (1 : G) ∈ N.normal.carrier :=
  N.contains_one


/-- `N` refines `M` when its kernel is contained in `M`; then `G/N` maps to `G/M`. -/
def oNSubgro.refines {G : Type u} [Group G] {T : pTopo G}
    (N M : oNSubgro G T) : Prop :=
  N.normal.carrier ≤ M.normal.carrier

/-- Transition map between finite quotients attached to nested open normal subgroups. -/
noncomputable def oNSubgro.transition {G : Type u} [Group G] {T : pTopo G}
    {N M : oNSubgro G T} (h : N.refines M) :
    quotientGroup N.normal →* quotientGroup M.normal :=
  quotientMapLE N.normal M.normal h

@[simp] theorem oNSubgro.transition_mk {G : Type u} [Group G]
    {T : pTopo G} {N M : oNSubgro G T} (h : N.refines M) (g : G) :
    oNSubgro.transition h (N.projection g) = M.projection g := by
  simpa [oNSubgro.transition, oNSubgro.projection]
    using quotient_mk N.normal M.normal h g

/-- Compatibility of quotient projections with the transition map. -/
theorem oNSubgro.transition_comp_projection {G : Type u} [Group G]
    {T : pTopo G} {N M : oNSubgro G T} (h : N.refines M) :
    (oNSubgro.transition h).comp N.projection = M.projection := by
  ext g
  exact oNSubgro.transition_mk h g

/-- Transition maps between nested open-normal quotients are surjective. -/
theorem oNSubgro.transition_surj {G : Type u} [Group G]
    {T : pTopo G} {N M : oNSubgro G T} (h : N.refines M) :
    Function.Surjective (oNSubgro.transition h) :=
  of_le_surjective N.normal M.normal h



@[refl] theorem oNSubgro.refines_refl {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) : N.refines N := le_rfl

@[trans] theorem oNSubgro.refines_trans {G : Type u} [Group G]
    {T : pTopo G} {N M K : oNSubgro G T}
    (hNM : N.refines M) (hMK : M.refines K) : N.refines K := le_trans hNM hMK

@[simp] theorem oNSubgro.transition_self {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) :
    oNSubgro.transition (N.refines_refl) = MonoidHom.id (quotientGroup N.normal) := by
  exact quotient_self N.normal

@[simp] theorem oNSubgro.transition_comp {G : Type u} [Group G]
    {T : pTopo G} {N M K : oNSubgro G T}
    (hNM : N.refines M) (hMK : M.refines K) :
    (oNSubgro.transition hMK).comp (oNSubgro.transition hNM) =
      oNSubgro.transition (oNSubgro.refines_trans hNM hMK) := by
  ext g
  simp [oNSubgro.transition]

/-- The open-normal neighborhoods are directed by refinement. -/
theorem oNSubgro.commonRefinement {G : Type u} [Group G]
    {T : pTopo G} (N M : oNSubgro G T) :
    ∃ K : oNSubgro G T, K.refines N ∧ K.refines M := by
  classical
  obtain ⟨K, hKopen, hKsub, hKfin⟩ :=
    T.openNormalBasis ((N.normal.carrier : Set G) ∩ (M.normal.carrier : Set G))
      (T.topology.isOpen_inter N.isOpen' M.isOpen')
      ⟨N.contains_one, M.contains_one⟩
  refine ⟨oNSubgro.ofNormal K hKopen hKfin, ?_, ?_⟩
  · intro x hx
    exact (hKsub hx).1
  · intro x hx
    exact (hKsub hx).2

/-- A profinite realization layer: finite quotient layers, continuous
projections, and compatibility with transition maps. -/
structure pRLayer (G : Type u) [Group G] where
  top : pTopo G
  layers : fLayers.{u}
  layerTopology : ∀ n, bTopo (layers.layer n)
  projection : ∀ n, G →* layers.layer n
  projection_surjective : ∀ n, Function.Surjective (projection n)
  projection_continuous : ∀ n, basicContinuous top.topology (layerTopology n) (projection n)
  compatible : ∀ {m n : ℕ} (h : m ≤ n), (layers.transition h).comp (projection n) = projection m


/-- Pointwise form of compatibility in a profinite realization layer. -/
theorem pRLayer.compat_apply {G : Type u} [Group G]
    (L : pRLayer G) {m n : ℕ} (h : m ≤ n) (g : G) :
    L.layers.transition h (L.projection n g) = L.projection m g := by
  have H := L.compatible h
  exact congrArg (fun f : G →* L.layers.layer m => f g) H

/-- Each realization projection is continuous, as a named theorem. -/
theorem pRLayer.projection_is_continuous {G : Type u} [Group G]
    (L : pRLayer G) (n : ℕ) :
    basicContinuous L.top.topology (L.layerTopology n) (L.projection n) :=
  L.projection_continuous n

/-- Each realization projection is surjective. -/
theorem pRLayer.projection_surj {G : Type u} [Group G]
    (L : pRLayer G) (n : ℕ) :
    Function.Surjective (L.projection n) :=
  L.projection_surjective n


/-- A continuous group homomorphism for lightweight topologies. -/
structure cHom (G : Type u) (H : Type v)
    [Group G] [Group H] (TG : pTopo G) (TH : pTopo H) where
  hom : G →* H
  continuous' : basicContinuous TG.topology TH.topology hom
  kernel_closed : TG.topology.IsOpen ((MonoidHom.ker hom : Set G)ᶜ)

/-- Named continuity projection for a continuous homomorphism. -/
theorem cHom.continuous {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cHom G H TG TH) :
    basicContinuous TG.topology TH.topology f.hom :=
  f.continuous'

/-- Named preimage-open projection for a continuous homomorphism. -/
theorem cHom.isOpen_preimage {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cHom G H TG TH) {U : Set H} (hU : TH.topology.IsOpen U) :
    TG.topology.IsOpen (f.hom ⁻¹' U) :=
  f.continuous' U hU

/-- The complement of the kernel is open in the source topology. -/
theorem cHom.kernel_compl_open {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cHom G H TG TH) :
    TG.topology.IsOpen ((MonoidHom.ker f.hom : Set G)ᶜ) :=
  f.kernel_closed


/-- Compose continuous homomorphisms in the lightweight profinite interface. -/
def cHom.comp {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (g : cHom H K TH TK)
    (f : cHom G H TG TH) :
    cHom G K TG TK where
  hom := g.hom.comp f.hom
  continuous' :=
    basicContinuous_comp TG.topology TH.topology TK.topology f.continuous' g.continuous'
  kernel_closed := by
    have hpre : TG.topology.IsOpen (f.hom ⁻¹' ((MonoidHom.ker g.hom : Set H)ᶜ)) :=
      f.continuous' ((MonoidHom.ker g.hom : Set H)ᶜ) g.kernel_closed
    simpa [MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply] using hpre

@[simp] theorem cHom.comp_apply {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (g : cHom H K TH TK)
    (f : cHom G H TG TH) (x : G) :
    (g.comp f).hom x = g.hom (f.hom x) := rfl

@[simp] theorem cHom.comp_hom {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (g : cHom H K TH TK)
    (f : cHom G H TG TH) :
    (g.comp f).hom = g.hom.comp f.hom := rfl

/-- Identity continuous homomorphism for a lightweight profinite topology. -/
def cHom.id (G : Type u) [Group G] (T : pTopo G) :
    cHom G G T T where
  hom := MonoidHom.id G
  continuous' := basicContinuous_id T.topology
  kernel_closed := by
    have hker :
        ((MonoidHom.ker (MonoidHom.id G) : Subgroup G) : Set G) = ({1} : Set G) := by
      ext x
      simp
    -- In a profinite (T2) group, `{1}` is closed, so its complement is open via
    -- total disconnectedness.
    -- Use the clopen separator for each nonidentity point and take their union.
    let C : Set (Set G) := {V | ∃ x : G, x ≠ 1 ∧ T.topology.IsOpen V ∧ x ∈ V ∧ (1 : G) ∉ V}
    have hopenC : ∀ V ∈ C, T.topology.IsOpen V := by
      intro V hV
      rcases hV with ⟨x, hx, hVo, hxV, h1V⟩
      exact hVo
    have hcover : (({1} : Set G)ᶜ) = ⋃₀ C := by
      ext x
      constructor
      · intro hx
        have hxne : x ≠ 1 := by simpa using hx
        rcases T.totallyDisconnected x 1 hxne with ⟨U, hUo, hUco, hxU, h1not⟩
        refine ⟨U, ?_, hxU⟩
        exact ⟨x, hxne, hUo, hxU, h1not⟩
      · intro hx
        rcases hx with ⟨V, hVC, hxV⟩
        rcases hVC with ⟨y, hy, hVo, hyV, h1V⟩
        intro hxeq
        subst x
        exact h1V hxV
    rw [hker, hcover]
    exact T.topology.sUnion_open C hopenC

@[simp] theorem cHom.id_hom (G : Type u) [Group G]
    (T : pTopo G) :
    (cHom.id G T).hom = MonoidHom.id G := rfl

/-- The trivial homomorphism is continuous for any lightweight profinite topologies. -/
def cHom.trivial (G : Type u) (H : Type v) [Group G] [Group H]
    (TG : pTopo G) (TH : pTopo H) :
    cHom G H TG TH where
  hom := 1
  continuous' := basicContinuous_const TG.topology TH.topology 1
  kernel_closed := by
    have hker : (((MonoidHom.ker (1 : G →* H)) : Subgroup G) : Set G) = Set.univ := by
      ext x
      simp
    simpa [hker] using TG.topology.isOpen_empty

@[simp] theorem cHom.trivial_hom (G : Type u) (H : Type v)
    [Group G] [Group H] (TG : pTopo G) (TH : pTopo H) :
    (cHom.trivial G H TG TH).hom = (1 : G →* H) := rfl

/-- An open map between lightweight topological spaces. -/
abbrev openMap {X : Type u} {Y : Type v} (TX : bTopo X) (TY : bTopo Y)
    (f : X → Y) : Prop :=
  basicOpenMap TX TY f

/-- A homomorphism that is both continuous and open. -/
structure cOMaps (G : Type u) (H : Type v)
    [Group G] [Group H] (TG : pTopo G) (TH : pTopo H) where
  hom : G →* H
  continuous' : basicContinuous TG.topology TH.topology hom
  open' : basicOpenMap TG.topology TH.topology hom
  kernel_closed : TG.topology.IsOpen ((MonoidHom.ker hom : Set G)ᶜ)

/-- Named continuity projection for a continuous-open homomorphism. -/
theorem cOMaps.continuous {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cOMaps G H TG TH) :
    basicContinuous TG.topology TH.topology f.hom :=
  f.continuous'

/-- Named openness projection for a continuous-open homomorphism. -/
theorem cOMaps.open_map {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cOMaps G H TG TH) :
    basicOpenMap TG.topology TH.topology f.hom :=
  f.open'

/-- Images of open sets are open under a continuous-open homomorphism. -/
theorem cOMaps.isOpen_image {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cOMaps G H TG TH) {U : Set G} (hU : TG.topology.IsOpen U) :
    TH.topology.IsOpen (f.hom '' U) :=
  f.open' U hU


/-- Identity continuous-open homomorphism. -/
def cOMaps.id (G : Type u) [Group G] (T : pTopo G) :
    cOMaps G G T T where
  hom := MonoidHom.id G
  continuous' := basicContinuous_id T.topology
  open' := basic_open_id T.topology
  kernel_closed := (cHom.id G T).kernel_closed

@[simp] theorem cOMaps.id_hom (G : Type u) [Group G]
    (T : pTopo G) :
    (cOMaps.id G T).hom = MonoidHom.id G := rfl

/-- Composition of continuous-open homomorphisms. -/
def cOMaps.comp {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (g : cOMaps H K TH TK) (f : cOMaps G H TG TH) :
    cOMaps G K TG TK where
  hom := g.hom.comp f.hom
  continuous' :=
    basicContinuous_comp TG.topology TH.topology TK.topology f.continuous' g.continuous'
  open' := basic_open_comp TG.topology TH.topology TK.topology f.open' g.open'
  kernel_closed := by
    have hpre : TG.topology.IsOpen (f.hom ⁻¹' ((MonoidHom.ker g.hom : Set H)ᶜ)) :=
      f.continuous' ((MonoidHom.ker g.hom : Set H)ᶜ) g.kernel_closed
    simpa [MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply] using hpre

@[simp] theorem cOMaps.comp_apply {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (g : cOMaps H K TH TK) (f : cOMaps G H TG TH) (x : G) :
    (g.comp f).hom x = g.hom (f.hom x) := rfl

/-- Forget openness from a continuous open homomorphism. -/
def cOMaps.toContinuousHomomorphism {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cOMaps G H TG TH) : cHom G H TG TH where
  hom := f.hom
  continuous' := f.continuous'
  kernel_closed := f.kernel_closed

@[simp] theorem cOMaps.cont_hom_hom {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cOMaps G H TG TH) :
    f.toContinuousHomomorphism.hom = f.hom := rfl

/-- An open neighborhood of the identity in a lightweight topology. -/
def oNId (G : Type u) [One G] (T : bTopo G) : Set (Set G) :=
  {U | T.IsOpen U ∧ (1 : G) ∈ U}


/-- Membership in the identity-neighborhood filter, unfolded. -/
theorem oNId.mem_iff {G : Type u} [One G]
    {T : bTopo G} {U : Set G} :
    U ∈ oNId G T ↔ T.IsOpen U ∧ (1 : G) ∈ U := Iff.rfl

/-- The whole space is an identity neighborhood. -/
theorem oNId.univ_mem (G : Type u) [One G] (T : bTopo G) :
    Set.univ ∈ oNId G T := by
  exact ⟨T.isOpen_univ, Set.mem_univ _⟩

/-- Identity neighborhoods are closed under binary intersection. -/
theorem oNId.inter_mem {G : Type u} [One G] {T : bTopo G}
    {U V : Set G} (hU : U ∈ oNId G T)
    (hV : V ∈ oNId G T) :
    U ∩ V ∈ oNId G T := by
  rcases hU with ⟨hUopen, hUone⟩
  rcases hV with ⟨hVopen, hVone⟩
  exact ⟨T.isOpen_inter hUopen hVopen, ⟨hUone, hVone⟩⟩


end Topology
end Towers
