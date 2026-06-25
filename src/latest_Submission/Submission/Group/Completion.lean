import Submission.Group.GolodShafarevich

namespace Submission
namespace Group

universe u v w
open Submission.Topology

/-- A finite nilpotent quotient package. -/
structure fNQuot (G : Type u) [Group G] where
  quotient : nSubgro G
  projection : G →* (G ⧸ quotient.carrier) := QuotientGroup.mk' quotient.carrier
  projection_surjective : Function.Surjective projection := by
    simpa [projection] using QuotientGroup.mk'_surjective quotient.carrier
  finite' : Finite (G ⧸ quotient.carrier)
  nilpotencyClass : ℕ
  nilpotencyClass_pos : 0 < nilpotencyClass
  /-- Convention: class `c` means the `(c+1)`st lower-central term vanishes. -/
  nilpotent : Subgroup.lowerCentralSeries (G ⧸ quotient.carrier) (nilpotencyClass + 1) = ⊥
  class_minimal : ∀ c, c ≤ nilpotencyClass →
    Subgroup.lowerCentralSeries (G ⧸ quotient.carrier) c ≠ ⊥
  kernel_eq : MonoidHom.ker projection = quotient.carrier

/-- The quotient projection is surjective. -/
theorem fNQuot.projection_surj {G : Type u} [Group G]
    (Q : fNQuot G) : Function.Surjective Q.projection :=
  Q.projection_surjective

/-- The recorded nilpotency class is positive. -/
theorem fNQuot.class_pos {G : Type u} [Group G]
    (Q : fNQuot G) : 0 < Q.nilpotencyClass :=
  Q.nilpotencyClass_pos

/-- The lower central series vanishes at one more than the recorded class. -/
theorem fNQuot.nilpotent_succ_class {G : Type u} [Group G]
    (Q : fNQuot G) :
    Subgroup.lowerCentralSeries (G ⧸ Q.quotient.carrier) (Q.nilpotencyClass + 1) = ⊥ :=
  Q.nilpotent


/-- Refa relation for finite nilpotent quotients by kernel inclusion. -/
def fNQuot.refines {G : Type u} [Group G]
    (Q R : fNQuot G) : Prop :=
  Q.quotient.carrier ≤ R.quotient.carrier

/-- Membership in the kernel of a finite nilpotent quotient projection. -/
theorem fNQuot.mem_kernel_iff {G : Type u} [Group G]
    (Q : fNQuot G) (g : G) :
    g ∈ MonoidHom.ker Q.projection ↔ g ∈ Q.quotient.carrier := by
  rw [Q.kernel_eq]

/-- Terms up to the recorded nilpotency class are nontrivial. -/
theorem fNQuot.class_min_nebot {G : Type u} [Group G]
    (Q : fNQuot G) {c : ℕ} (hc : c ≤ Q.nilpotencyClass) :
    Subgroup.lowerCentralSeries (G ⧸ Q.quotient.carrier) c ≠ ⊥ :=
  Q.class_minimal c hc

/-- The quotient type of a finite nilpotent quotient is finite. -/
theorem fNQuot.finite_quotient' {G : Type u} [Group G]
    (Q : fNQuot G) : Finite (G ⧸ Q.quotient.carrier) :=
  Q.finite'

/-- The induced map between nested finite nilpotent quotients. -/
noncomputable def fNQuot.transition {G : Type u} [Group G]
    {Q R : fNQuot G} (h : Q.refines R) :
    (G ⧸ Q.quotient.carrier) →* (G ⧸ R.quotient.carrier) :=
  quotientMapLE Q.quotient R.quotient h

@[simp] theorem fNQuot.transition_mk {G : Type u} [Group G]
    {Q R : fNQuot G} (h : Q.refines R) (g : G) :
    fNQuot.transition h (QuotientGroup.mk' Q.quotient.carrier g) =
      QuotientGroup.mk' R.quotient.carrier g := by
  simpa [fNQuot.transition]
    using quotient_mk Q.quotient R.quotient h g


@[refl] theorem fNQuot.refines_refl {G : Type u} [Group G]
    (Q : fNQuot G) : Q.refines Q := le_rfl

@[trans] theorem fNQuot.refines_trans {G : Type u} [Group G]
    {Q R S : fNQuot G} (hQR : Q.refines R) (hRS : R.refines S) :
    Q.refines S := le_trans hQR hRS

/-- Transition maps between nested finite nilpotent quotients are surjective. -/
theorem fNQuot.transition_surjective {G : Type u} [Group G]
    {Q R : fNQuot G} (h : Q.refines R) :
    Function.Surjective (fNQuot.transition h) :=
  of_le_surjective Q.quotient R.quotient h

@[simp] theorem fNQuot.transition_self {G : Type u} [Group G]
    (Q : fNQuot G) :
    fNQuot.transition (Q.refines_refl) =
      MonoidHom.id (G ⧸ Q.quotient.carrier) := by
  exact quotient_self Q.quotient


@[simp] theorem fNQuot.transition_comp {G : Type u} [Group G]
    {Q R S : fNQuot G} (hQR : Q.refines R) (hRS : R.refines S) :
    (fNQuot.transition hRS).comp
      (fNQuot.transition hQR) =
    fNQuot.transition (fNQuot.refines_trans hQR hRS) := by
  ext g
  simp [fNQuot.transition]

/-- Dense generated subgroup in a lightweight topology. -/
structure dGSubgro (G : Type u) [Group G] (T : pTopo G) where
  generators : Set G
  generated : Subgroup G
  generated_eq_closure : generated = Subgroup.closure generators
  /-- Topological density is the generation condition; we deliberately do not
  require `generated = ⊤`, which would be algebraic generation. -/
  dense : bDense T.topology (generated : Set G)
  generators_subset : generators ⊆ generated

/-- Displayed generators lie in the generated subgroup. -/
theorem dGSubgro.generator_mem {G : Type u} [Group G]
    {T : pTopo G} (D : dGSubgro G T) {g : G}
    (hg : g ∈ D.generators) : g ∈ D.generated :=
  D.generators_subset hg

/-- The algebraic subgroup need not be all of `G`; topological generation is
recorded by density instead. -/
theorem dGSubgro.generated_is_closure {G : Type u} [Group G]
    {T : pTopo G} (D : dGSubgro G T) :
    D.generated = Subgroup.closure D.generators :=
  D.generated_eq_closure

/-- The generated subgroup is the algebraic closure of the displayed generators. -/
theorem dGSubgro.generated_eq_closure' {G : Type u} [Group G]
    {T : pTopo G} (D : dGSubgro G T) :
    D.generated = Subgroup.closure D.generators :=
  D.generated_eq_closure

/-- The generated subgroup is dense. -/
theorem dGSubgro.dense_generated {G : Type u} [Group G]
    {T : pTopo G} (D : dGSubgro G T) :
    bDense T.topology (D.generated : Set G) :=
  D.dense

/-- A topological generating set. -/
structure tGSet (G : Type u) [Group G] (T : pTopo G) where
  carrier : Set G
  denseGenerated : dGSubgro G T
  carrier_eq : carrier = denseGenerated.generators
  dense_closure : bDense T.topology (denseGenerated.generated : Set G)

/-- Canonical topological generating set associated to a dense generated subgroup. -/
def tGSet.ofDenseGenerated {G : Type u} [Group G]
    {T : pTopo G} (D : dGSubgro G T) :
    tGSet G T where
  carrier := D.generators
  denseGenerated := D
  carrier_eq := rfl
  dense_closure := D.dense

@[simp] theorem tGSet.dense_gen_carrier {G : Type u} [Group G]
    {T : pTopo G} (D : dGSubgro G T) :
    (tGSet.ofDenseGenerated D).carrier = D.generators := rfl

/-- The redundant density field agrees with the density stored in the underlying package
for canonically constructed topological generating sets. -/
theorem tGSet.dense_gen_dense {G : Type u} [Group G]
    {T : pTopo G} (D : dGSubgro G T) :
    (tGSet.ofDenseGenerated D).dense_closure = D.dense := rfl

/-- Membership in the carrier is membership in the displayed generator set. -/
theorem tGSet.mem_carrier_iff {G : Type u} [Group G]
    {T : pTopo G} (S : tGSet G T) {g : G} :
    g ∈ S.carrier ↔ g ∈ S.denseGenerated.generators := by
  rw [S.carrier_eq]

/-- Carrier elements lie in the generated subgroup. -/
theorem tGSet.carrier_mem_generated {G : Type u} [Group G]
    {T : pTopo G} (S : tGSet G T) {g : G}
    (hg : g ∈ S.carrier) : g ∈ S.denseGenerated.generated := by
  exact S.denseGenerated.generator_mem ((S.mem_carrier_iff).1 hg)

/-- The displayed generated subgroup is dense. -/
theorem tGSet.generated_dense {G : Type u} [Group G]
    {T : pTopo G} (S : tGSet G T) :
    bDense T.topology (S.denseGenerated.generated : Set G) :=
  S.dense_closure


/-- Topological finite generation by a finite set: its abstract subgroup and
closure are dense in the profinite topology. -/
structure tFGenera (G : Type u) [Group G] (T : pTopo G) where
  gens : Finset G
  generated : Subgroup G
  generated_eq_closure : generated = Subgroup.closure (↑gens : Set G)
  dense : bDense T.topology (generated : Set G)
  contains_generators : (↑gens : Set G) ⊆ generated
  /-- Equivalently, the images generate every finite open-normal quotient. -/
  quotient_images_generate : ∀ N : oNSubgro G T,
    Subgroup.closure ((QuotientGroup.mk' N.normal.carrier) '' (↑gens : Set G)) = ⊤

/-- Finite topological generators lie in their generated subgroup. -/
theorem tFGenera.mem_gen_memgens {G : Type u} [Group G]
    {T : pTopo G} (F : tFGenera G T) {g : G}
    (hg : g ∈ (↑F.gens : Set G)) : g ∈ F.generated :=
  F.contains_generators hg

/-- Images of finite topological generators generate every open-normal quotient. -/
theorem tFGenera.quotient_images_generate' {G : Type u} [Group G]
    {T : pTopo G} (F : tFGenera G T)
    (N : oNSubgro G T) :
    Subgroup.closure ((QuotientGroup.mk' N.normal.carrier) '' (↑F.gens : Set G)) = ⊤ :=
  F.quotient_images_generate N

/-- The subgroup generated by a finite topological generating set is dense. -/
theorem tFGenera.generated_dense {G : Type u} [Group G]
    {T : pTopo G} (F : tFGenera G T) :
    bDense T.topology (F.generated : Set G) :=
  F.dense

/-- Forget finiteness from a finite topological generating set, retaining the dense
generated subgroup. -/
def tFGenera.dense_gen_subgroup {G : Type u} [Group G]
    {T : pTopo G} (F : tFGenera G T) :
    dGSubgro G T where
  generators := (↑F.gens : Set G)
  generated := F.generated
  generated_eq_closure := F.generated_eq_closure
  dense := F.dense
  generators_subset := F.contains_generators

/-- A finite topological generating set gives a (possibly non-finite) topological generating set. -/
def tFGenera.topo_gen_set {G : Type u} [Group G]
    {T : pTopo G} (F : tFGenera G T) :
    tGSet G T where
  carrier := (↑F.gens : Set G)
  denseGenerated := F.dense_gen_subgroup
  carrier_eq := rfl
  dense_closure := F.dense

@[simp] theorem tFGenera.toDense_generators {G : Type u} [Group G]
    {T : pTopo G} (F : tFGenera G T) :
    F.dense_gen_subgroup.generators = (↑F.gens : Set G) := rfl

@[simp] theorem tFGenera.toTopological_carrier {G : Type u} [Group G]
    {T : pTopo G} (F : tFGenera G T) :
    F.topo_gen_set.carrier = (↑F.gens : Set G) := rfl

/-- A genuinely general finite-index subgroup, without a normality requirement.
The older `fISubgro` below is retained for normal subgroups because it
also packages a quotient group and projection. -/
structure gISubgro (G : Type u) [Group G] where
  subgroup : Subgroup G
  [finiteIndex : subgroup.FiniteIndex]
  index : ℕ
  index_eq : index = subgroup.index

attribute [instance] gISubgro.finiteIndex

/-- The index of a general finite-index subgroup is nonzero. -/
theorem gISubgro.index_ne_zero {G : Type u} [Group G]
    (H : gISubgro G) : H.index ≠ 0 := by
  rw [H.index_eq]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- Hence the recorded index is positive. -/
theorem gISubgro.index_pos {G : Type u} [Group G]
    (H : gISubgro G) : 0 < H.index :=
  Nat.pos_of_ne_zero H.index_ne_zero

/-- Build the general package from any subgroup with a finite-index instance. -/
noncomputable def gISubgro.ofSubgroup {G : Type u} [Group G]
    (H : Subgroup G) [H.FiniteIndex] : gISubgro G where
  subgroup := H
  index := H.index
  index_eq := rfl

/-- A finite-index subgroup, packaged by finiteness of the quotient. -/
structure fISubgro (G : Type u) [Group G] where
  subgroup : Subgroup G
  normal' : subgroup.Normal
  finiteQuotient : Finite (G ⧸ subgroup)
  projection : G →* (G ⧸ subgroup) := QuotientGroup.mk' subgroup
  projection_surjective : Function.Surjective projection
  index : ℕ := Nat.card (G ⧸ subgroup)
  index_eq_card : index = Nat.card (G ⧸ subgroup)
  positive_index : 0 < index

attribute [instance] fISubgro.normal'

/-- Forget normality/quotient-map data from the normal finite-index package. -/
noncomputable def fISubgro.toGeneral {G : Type u} [Group G]
    (H : fISubgro G) : gISubgro G := by
  classical
  letI := H.finiteQuotient
  haveI : H.subgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact gISubgro.ofSubgroup H.subgroup

@[simp] theorem fISubgro.toGeneral_subgroup {G : Type u} [Group G]
    (H : fISubgro G) : H.toGeneral.subgroup = H.subgroup := rfl

/-- The projection of a finite-index subgroup is surjective. -/
theorem fISubgro.projection_surj {G : Type u} [Group G]
    (H : fISubgro G) : Function.Surjective H.projection :=
  H.projection_surjective

/-- The recorded index is positive. -/
theorem fISubgro.index_pos {G : Type u} [Group G]
    (H : fISubgro G) : 0 < H.index :=
  H.positive_index

/-- The recorded index is the cardinality of the quotient. -/
theorem fISubgro.index_spec {G : Type u} [Group G]
    (H : fISubgro G) : H.index = Nat.card (G ⧸ H.subgroup) :=
  H.index_eq_card



/-- A finite normal subgroup quotient gives a finite-index subgroup package. -/
noncomputable def fISubgro.ofNormal {G : Type u} [Group G]
    (N : nSubgro G) (hfin : Finite (G ⧸ N.carrier)) : fISubgro G where
  subgroup := N.carrier
  normal' := N.normal'
  finiteQuotient := hfin
  projection := QuotientGroup.mk' N.carrier
  projection_surjective := by simpa using QuotientGroup.mk'_surjective N.carrier
  index := Nat.card (G ⧸ N.carrier)
  index_eq_card := rfl
  positive_index := by
    classical
    haveI := hfin
    exact Nat.card_pos


@[simp] theorem fISubgro.ofNormal_subgroup {G : Type u} [Group G]
    (N : nSubgro G) (hfin : Finite (G ⧸ N.carrier)) :
    (fISubgro.ofNormal N hfin).subgroup = N.carrier := rfl

@[simp] theorem fISubgro.normal_projection_apply {G : Type u} [Group G]
    (N : nSubgro G) (hfin : Finite (G ⧸ N.carrier)) (g : G) :
    (fISubgro.ofNormal N hfin).projection g = QuotientGroup.mk' N.carrier g := rfl

@[simp] theorem fISubgro.ofNormal_index {G : Type u} [Group G]
    (N : nSubgro G) (hfin : Finite (G ⧸ N.carrier)) :
    (fISubgro.ofNormal N hfin).index = Nat.card (G ⧸ N.carrier) := rfl

end Group
namespace Topology

/-- An open normal subgroup in a profinite topology is, in particular, finite-index. -/
noncomputable def oNSubgro.toFiniteIndex {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) :
    Submission.Group.fISubgro G :=
  Submission.Group.fISubgro.ofNormal N.normal N.finiteQuotient

@[simp] theorem oNSubgro.fin_index_subgroup {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) :
    N.toFiniteIndex.subgroup = N.normal.carrier := rfl

end Topology
namespace Group
open Submission.Topology

/-- Abstract finite quotient of a profinite group, with its kernel and quotient
identification recorded explicitly. -/
structure aFQuot (G : Type u) [Group G] where
  target : Type v
  [group_target : Group target]
  [finite_target : Finite target]
  map : G →* target
  surjective : Function.Surjective map
  kernel : Subgroup G := MonoidHom.ker map
  kernel_eq : kernel = MonoidHom.ker map
  kernel_normal : kernel.Normal
  quotientEquiv : (G ⧸ kernel) ≃* target
  quotient_comm : ∀ g : G, quotientEquiv (QuotientGroup.mk g) = map g

attribute [instance] aFQuot.group_target aFQuot.finite_target


/-- Canonical abstract finite quotient associated to a surjection onto a finite group. -/
noncomputable def aFQuot.ofSurjective {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite H] (f : G →* H) (hf : Function.Surjective f) :
    aFQuot G where
  target := H
  group_target := inferInstance
  finite_target := inferInstance
  map := f
  surjective := hf
  kernel := MonoidHom.ker f
  kernel_eq := rfl
  kernel_normal := inferInstance
  quotientEquiv := QuotientGroup.quotientKerEquivOfSurjective (φ := f) hf
  quotient_comm := by
    intro g
    simp [QuotientGroup.quotientKerEquivOfSurjective,
      QuotientGroup.quotientKerEquivOfRightInverse]

@[simp] theorem aFQuot.ofSurjective_map {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite H] (f : G →* H) (hf : Function.Surjective f) :
    (aFQuot.ofSurjective f hf).map = f := rfl

end Group
namespace Topology

/-- Forget the topology on a finite continuous quotient, retaining its canonical abstract
finite quotient package. -/
noncomputable def fCQuota.abstract_fin_quot {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    Submission.Group.aFQuot G :=
  Submission.Group.aFQuot.ofSurjective Q.map Q.surjective

@[simp] theorem fCQuota.abstract_fin_quotmap {G : Type u}
    [Group G] {TG : pTopo G} (Q : fCQuota G TG) :
    Q.abstract_fin_quot.map = Q.map := rfl

end Topology
namespace Group
open Submission.Topology

/-- The quotient by a finite normal subgroup is an abstract finite quotient. -/
def aFQuot.ofNormal {G : Type u} [Group G]
    (N : nSubgro G) (hfin : Finite (quotientGroup N)) :
    aFQuot G where
  target := quotientGroup N
  group_target := inferInstance
  finite_target := hfin
  map := N.projection
  surjective := N.projection_surjective
  kernel := N.carrier
  kernel_eq := N.ker_projection.symm
  kernel_normal := N.normal'
  quotientEquiv := MulEquiv.refl _
  quotient_comm := by
    intro g
    rfl


@[simp] theorem aFQuot.ofNormal_map {G : Type u} [Group G]
    (N : nSubgro G) (hfin : Finite (quotientGroup N)) (g : G) :
    (aFQuot.ofNormal N hfin).map g = N.projection g := rfl

@[simp] theorem aFQuot.ofNormal_kernel {G : Type u} [Group G]
    (N : nSubgro G) (hfin : Finite (quotientGroup N)) :
    (aFQuot.ofNormal N hfin).kernel = N.carrier := rfl

/-- The map of an abstract finite quotient is surjective. -/
theorem aFQuot.map_surjective {G : Type u} [Group G]
    (Q : aFQuot G) : Function.Surjective Q.map :=
  Q.surjective


/-- Forget an abstract finite quotient to the underlying packaged epimorphism, transporting
along the recorded kernel equality. -/
noncomputable def aFQuot.toSurjectiveHomomorphism {G : Type u} [Group G]
    (Q : aFQuot G) : sHoma G Q.target where
  hom := Q.map
  surjective := Q.surjective
  quotientEquiv := by
    letI : Q.kernel.Normal := Q.kernel_normal
    exact (QuotientGroup.quotientMulEquivOfEq Q.kernel_eq.symm).trans Q.quotientEquiv
  quotient_comm := by
    intro g
    letI : Q.kernel.Normal := Q.kernel_normal
    simpa [QuotientGroup.quotientMulEquivOfEq_mk] using Q.quotient_comm g

@[simp] theorem aFQuot.surj_hom_hom {G : Type u}
    [Group G] (Q : aFQuot G) :
    Q.toSurjectiveHomomorphism.hom = Q.map := rfl

/-- The quotient equivalence commutes with the quotient projection. -/
theorem aFQuot.quotient_comm_apply {G : Type u} [Group G]
    (Q : aFQuot G) (g : G) :
    Q.quotientEquiv (QuotientGroup.mk g) = Q.map g :=
  Q.quotient_comm g

/-- The kernel recorded by an abstract finite quotient is normal. -/
theorem aFQuot.kernel_normal' {G : Type u} [Group G]
    (Q : aFQuot G) : Q.kernel.Normal :=
  Q.kernel_normal

/-- Profinite completion viewpoint as an inverse system, with dense/surjective
finite-level coordinates recorded as the defining approximation property. -/
structure pCViewpo (G : Type u) [Group G] where
  system : cSQuotie.{u}
  comparison : G →* inverseLimit system
  coordinate : ∀ n, G →* system.obj n :=
    fun n => (inverseLimitProjection system n).comp comparison
  coordinate_surjective : ∀ n, Function.Surjective (coordinate n)
  compatible_coordinates : ∀ {m n : ℕ} (h : m ≤ n),
    (system.map h).comp (coordinate n) = coordinate m

/-- The subgroup given by the intersection of all terms of a descending filtration. -/
def filtrationIntersection {G : Type u} [Group G] (F : DFilt G) : Subgroup G where
  carrier := {x | ∀ n, x ∈ F n}
  one_mem' := by intro n; exact (F n).one_mem
  mul_mem' := by intro x y hx hy n; exact (F n).mul_mem (hx n) (hy n)
  inv_mem' := by intro x hx n; exact (F n).inv_mem (hx n)

/-- A separated filtration: the canonical intersection subgroup is trivial.
Unlike the earlier bookkeeping version, the intersection is not an independent
field, so the set/subgroup and pointwise formulations cannot disagree. -/
structure sFilt (G : Type u) [Group G] where
  filtration : DFilt G
  intersection_eq_bot : filtrationIntersection filtration = ⊥

/-- The canonical intersection subgroup of a separated filtration. -/
def sFilt.intersectionSubgroup {G : Type u} [Group G]
    (S : sFilt G) : Subgroup G :=
  filtrationIntersection S.filtration

/-- The underlying set of elements lying in every filtration term. -/
def sFilt.intersection {G : Type u} [Group G]
    (S : sFilt G) : Set G :=
  {x | ∀ n, x ∈ S.filtration n}

/-- In a separated filtration, an element lying in every term is trivial. -/
theorem sFilt.eq_one_memall {G : Type u} [Group G]
    (S : sFilt G) {x : G} (hx : ∀ n, x ∈ S.filtration n) : x = 1 := by
  have hxI : x ∈ filtrationIntersection S.filtration := hx
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [S.intersection_eq_bot] using hxI
  simpa using hxbot

/-- Pointwise separatedness, as a named accessor. -/
theorem sFilt.separated {G : Type u} [Group G]
    (S : sFilt G) (x : G) (hx : ∀ n, x ∈ S.filtration n) : x = 1 :=
  S.eq_one_memall hx

/-- The identity lies in every term of a separated filtration. -/
theorem sFilt.one_mem_all {G : Type u} [Group G]
    (S : sFilt G) : ∀ n, (1 : G) ∈ S.filtration n := by
  intro n
  exact (S.filtration n).one_mem

/-- Membership in the canonical intersection of a separated filtration forces triviality. -/
theorem sFilt.eq_one_meminter {G : Type u} [Group G]
    (S : sFilt G) {x : G}
    (hx : x ∈ filtrationIntersection S.filtration) : x = 1 :=
  S.eq_one_memall hx

/-- The intersection subgroup of a separated filtration is bottom. -/
theorem sFilt.inter_subgroup_eqbot {G : Type u} [Group G]
    (S : sFilt G) : S.intersectionSubgroup = ⊥ :=
  S.intersection_eq_bot

/-- The set-theoretic intersection of a separated filtration is `{1}`. -/
theorem sFilt.inter_set_eqone {G : Type u} [Group G]
    (S : sFilt G) : S.intersection = ({1} : Set G) := by
  ext x
  constructor
  · intro hx
    have hx1 : x = 1 := S.eq_one_memall hx
    rw [hx1]
    simp
  · intro hx
    rcases hx with rfl
    intro n
    exact (S.filtration n).one_mem

/-- A complete filtration: the comparison to the inverse limit is bijective and
its finite coordinates have the prescribed filtration kernels. -/
structure cFilt (G : Type u) [Group G] where
  filtration : DFilt G
  quotientSystem : cSQuotie.{u}
  comparison : G →* inverseLimit quotientSystem
  complete : Function.Surjective comparison
  separated_injective : Function.Injective comparison
  coordinate : ∀ n, G →* quotientSystem.obj n := fun n =>
    (inverseLimitProjection quotientSystem n).comp comparison
  coordinate_surjective : ∀ n, Function.Surjective (coordinate n)
  coordinate_compat : ∀ {m n : ℕ} (h : m ≤ n),
    (quotientSystem.map h).comp (coordinate n) = coordinate m
  kernel_terms : ∀ n, MonoidHom.ker (coordinate n) = filtration n


/-- Coordinates of a profinite completion viewpoint are surjective. -/
theorem pCViewpo.coordinate_surj {G : Type u} [Group G]
    (C : pCViewpo G) (n : ℕ) : Function.Surjective (C.coordinate n) :=
  C.coordinate_surjective n

/-- Coordinate compatibility as an equality of homomorphisms. -/
theorem pCViewpo.coordinate_compat {G : Type u} [Group G]
    (C : pCViewpo G) {m n : ℕ} (h : m ≤ n) :
    (C.system.map h).comp (C.coordinate n) = C.coordinate m :=
  C.compatible_coordinates h

/-- The comparison map of a complete filtration is surjective. -/
theorem cFilt.comparison_surj {G : Type u} [Group G]
    (C : cFilt G) : Function.Surjective C.comparison :=
  C.complete

/-- The comparison map of a complete filtration is injective. -/
theorem cFilt.comparison_inj {G : Type u} [Group G]
    (C : cFilt G) : Function.Injective C.comparison :=
  C.separated_injective

/-- Coordinates of a complete filtration are surjective. -/
theorem cFilt.coordinate_surj {G : Type u} [Group G]
    (C : cFilt G) (n : ℕ) : Function.Surjective (C.coordinate n) :=
  C.coordinate_surjective n

/-- Coordinate compatibility, pointwise form. -/
theorem pCViewpo.coordinate_compat_apply {G : Type u} [Group G]
    (C : pCViewpo G) {m n : ℕ} (h : m ≤ n) (g : G) :
    C.system.map h (C.coordinate n g) = C.coordinate m g := by
  have H := C.compatible_coordinates h
  exact congrArg (fun f : G →* C.system.obj m => f g) H

/-- Coordinate compatibility for a complete filtration, pointwise form. -/
theorem cFilt.coordinate_compat_apply {G : Type u} [Group G]
    (C : cFilt G) {m n : ℕ} (h : m ≤ n) (g : G) :
    C.quotientSystem.map h (C.coordinate n g) = C.coordinate m g := by
  have H := C.coordinate_compat h
  exact congrArg (fun f : G →* C.quotientSystem.obj m => f g) H


/-- In a complete filtration, membership in the nth term is the same as being
killed by the nth coordinate map. -/
theorem cFilt.memterm_iffcoord_eqone {G : Type u} [Group G]
    (C : cFilt G) (n : ℕ) (g : G) :
    g ∈ C.filtration n ↔ C.coordinate n g = 1 := by
  have h := congrArg (fun H : Subgroup G => g ∈ H) (C.kernel_terms n)
  change (g ∈ MonoidHom.ker (C.coordinate n)) = (g ∈ C.filtration n) at h
  have hk : (g ∈ MonoidHom.ker (C.coordinate n)) ↔ C.coordinate n g = 1 := Iff.rfl
  rw [← h]
  exact hk.symm

/-- Elements of a complete filtration term are killed by the corresponding coordinate. -/
theorem cFilt.coord_eq_onemem {G : Type u} [Group G]
    (C : cFilt G) {n : ℕ} {g : G} (hg : g ∈ C.filtration n) :
    C.coordinate n g = 1 :=
  (C.memterm_iffcoord_eqone n g).1 hg

/-- If a coordinate is trivial, the element lies in the corresponding filtration term. -/
theorem cFilt.mem_coord_eqone {G : Type u} [Group G]
    (C : cFilt G) {n : ℕ} {g : G} (hg : C.coordinate n g = 1) :
    g ∈ C.filtration n :=
  (C.memterm_iffcoord_eqone n g).2 hg

/-- The comparison map of a complete filtration is bijective. -/
theorem cFilt.comparison_bijective {G : Type u} [Group G]
    (C : cFilt G) : Function.Bijective C.comparison :=
  ⟨C.separated_injective, C.complete⟩

/-- Kernel equality for complete-filtration coordinates. -/
theorem cFilt.kernel_coordinate_eq {G : Type u} [Group G]
    (C : cFilt G) (n : ℕ) :
    MonoidHom.ker (C.coordinate n) = C.filtration n :=
  C.kernel_terms n

/-- Coordinate compatibility as a homomorphism equality. -/
theorem cFilt.coordinate_compat_hom {G : Type u} [Group G]
    (C : cFilt G) {m n : ℕ} (h : m ≤ n) :
    (C.quotientSystem.map h).comp (C.coordinate n) = C.coordinate m :=
  C.coordinate_compat h

/-- An open tail of a filtration in a lightweight profinite topology.
All sufficiently deep terms are recorded as open finite-index neighborhoods,
so the basis assertion is not tied to a single isolated term. -/
structure oFTerm (G : Type u) [Group G] (T : pTopo G) where
  filtration : DFilt G
  degree : ℕ
  open_above : ∀ n, degree ≤ n → T.topology.IsOpen (filtration n : Set G)
  finite_quotient_above : ∀ n (_h : degree ≤ n), Finite (G ⧸ filtration n)
  neighborhood_basis : ∀ U : Set G, T.topology.IsOpen U → (1 : G) ∈ U →
    ∃ n ≥ degree, (filtration n : Set G) ⊆ U

/-- The distinguished term is open. -/
def oFTerm.isOpen {G : Type u} [Group G] {T : pTopo G}
    (O : oFTerm G T) : T.topology.IsOpen (O.filtration O.degree : Set G) :=
  O.open_above O.degree (le_rfl)

/-- The distinguished term is normal (filtration terms are normal by definition). -/
theorem oFTerm.normal_term {G : Type u} [Group G] {T : pTopo G}
    (O : oFTerm G T) : (O.filtration O.degree).Normal :=
  O.filtration.normal' O.degree

/-- The quotient by the distinguished term is finite. -/
@[reducible] def oFTerm.finite_quotient {G : Type u} [Group G] {T : pTopo G}
    (O : oFTerm G T) : Finite (G ⧸ O.filtration O.degree) :=
  O.finite_quotient_above O.degree (le_rfl)

/-- The distinguished open filtration term contains the identity. -/
theorem oFTerm.one_mem {G : Type u} [Group G] {T : pTopo G}
    (O : oFTerm G T) : (1 : G) ∈ O.filtration O.degree :=
  (O.filtration O.degree).one_mem

/-- A named form of the neighborhood-basis property. -/
theorem oFTerm.exists_term_subset {G : Type u} [Group G]
    {T : pTopo G} (O : oFTerm G T)
    {U : Set G} (hU : T.topology.IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ n, O.degree ≤ n ∧ (O.filtration n : Set G) ⊆ U := by
  rcases O.neighborhood_basis U hU h1 with ⟨n, hn, hsub⟩
  exact ⟨n, hn, hsub⟩

/-- The displayed term is normal. -/
theorem oFTerm.normal {G : Type u} [Group G] {T : pTopo G}
    (O : oFTerm G T) : (O.filtration O.degree).Normal :=
  O.normal_term

/-- The distinguished filtration term is open. -/
theorem oFTerm.isOpen_term {G : Type u} [Group G] {T : pTopo G}
    (O : oFTerm G T) : T.topology.IsOpen (O.filtration O.degree : Set G) :=
  O.isOpen

/-- Every term in the recorded tail is open. -/
theorem oFTerm.isOpen_above {G : Type u} [Group G] {T : pTopo G}
    (O : oFTerm G T) {n : ℕ} (h : O.degree ≤ n) :
    T.topology.IsOpen (O.filtration n : Set G) :=
  O.open_above n h

/-- The quotient by the distinguished open term is finite. -/
theorem oFTerm.finite_quotient_term {G : Type u} [Group G]
    {T : pTopo G} (O : oFTerm G T) :
    Finite (G ⧸ O.filtration O.degree) :=
  O.finite_quotient

/-- Every term in the recorded tail has finite quotient. -/
theorem oFTerm.finite_quotient_above' {G : Type u} [Group G]
    {T : pTopo G} (O : oFTerm G T) {n : ℕ} (h : O.degree ≤ n) :
    Finite (G ⧸ O.filtration n) :=
  O.finite_quotient_above n h


/-- The filtration tail gives a left-coset neighborhood basis at every point, not just at
`1`, using continuity of left translations in the profinite topology. -/
theorem oFTerm.exists_left_cosetsubset {G : Type u} [Group G]
    {T : pTopo G} (O : oFTerm G T) {g : G} {U : Set G}
    (hU : T.topology.IsOpen U) (hg : g ∈ U) :
    ∃ n, O.degree ≤ n ∧ {x : G | ∃ k ∈ O.filtration n, x = g * k} ⊆ U := by
  let V : Set G := {x | g * x ∈ U}
  have hV : T.topology.IsOpen V := T.left_translate_continuous g U hU
  have h1 : (1 : G) ∈ V := by simpa [V] using hg
  rcases O.neighborhood_basis V hV h1 with ⟨n, hn, hsub⟩
  refine ⟨n, hn, ?_⟩
  intro x hx
  rcases hx with ⟨k, hk, rfl⟩
  exact hsub hk

/-- Right-coset version of the neighborhood basis at an arbitrary point. -/
theorem oFTerm.exists_right_cosetsubset {G : Type u} [Group G]
    {T : pTopo G} (O : oFTerm G T) {g : G} {U : Set G}
    (hU : T.topology.IsOpen U) (hg : g ∈ U) :
    ∃ n, O.degree ≤ n ∧ {x : G | ∃ k ∈ O.filtration n, x = k * g} ⊆ U := by
  let V : Set G := {x | x * g ∈ U}
  have hV : T.topology.IsOpen V := T.right_translate_continuous g U hU
  have h1 : (1 : G) ∈ V := by simpa [V] using hg
  rcases O.neighborhood_basis V hV h1 with ⟨n, hn, hsub⟩
  refine ⟨n, hn, ?_⟩
  intro x hx
  rcases hx with ⟨k, hk, rfl⟩
  exact hsub hk

/-- Membership in the intersection subgroup is pointwise membership in every term. -/
@[simp] theorem filtrationIntersection_mem {G : Type u} [Group G]
    (F : DFilt G) (x : G) :
    x ∈ filtrationIntersection F ↔ ∀ n, x ∈ F n := Iff.rfl

/-- The intersection of a filtration is contained in each term. -/
theorem filtration_intersection_term {G : Type u} [Group G]
    (F : DFilt G) (n : ℕ) :
    filtrationIntersection F ≤ F n := by
  intro x hx
  exact hx n

/-- Pointwise inclusion of filtrations induces inclusion of their intersections. -/
theorem filtrationIntersection_mono {G : Type u} [Group G]
    {F E : DFilt G} (h : ∀ n, F n ≤ E n) :
    filtrationIntersection F ≤ filtrationIntersection E := by
  intro x hx n
  exact h n (hx n)

/-- Two inverse-limit points are equal when all their finite coordinates are equal. -/
theorem inverseLimit_ext {S : cSQuotie.{u}}
    {x y : inverseLimit S}
    (h : ∀ n, inverseLimitProjection S n x = inverseLimitProjection S n y) : x = y := by
  apply Subtype.ext
  funext n
  exact h n

/-- The comparison map of a complete filtration is separated if its raw inverse-limit
coordinates agree. -/
theorem cFilt.eq_compare_coordseq {G : Type u} [Group G]
    (C : cFilt G) {x y : G}
    (h : ∀ n, inverseLimitProjection C.quotientSystem n (C.comparison x) =
      inverseLimitProjection C.quotientSystem n (C.comparison y)) : x = y := by
  apply C.separated_injective
  exact inverseLimit_ext h


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

/-- A finite nilpotent quotient realizes a filtration truncation by killing the next term. -/
def NilpotentRealizesTruncation {G : Type u} [Group G]
    (F : DFilt G) (Q : fNQuot G) (N : ℕ) : Prop :=
  Finite (G ⧸ Q.quotient.carrier) ∧ F (N + 1) ≤ Q.quotient.carrier
/-- A finite nilpotent quotient realizes a truncation when its kernel kills the next term. -/
theorem nilpotentRealizesTruncation {G : Type u} [Group G]
    (F : DFilt G) (Q : fNQuot G) (N : ℕ)
    (hkill : F (N + 1) ≤ Q.quotient.carrier) :
    Finite (G ⧸ Q.quotient.carrier) ∧ F (N + 1) ≤ Q.quotient.carrier
  := by
  constructor
  · exact Q.finite'
  · exact hkill
/-- A separated complete filtration recovers its object from the layers. -/
theorem recoversObjectLayers {G : Type u} [Group G]
    (F : DFilt G)
    (hfin : ∀ n, Finite (quotientGroup (filtrationNormalTerm F n)))
    (hseparated : filtrationIntersection F = ⊥)
    (hcomplete :
      ∀ y : inverseLimit (cSQuotie.ofFiltration F hfin),
        ∃ g : G, ∀ n,
          QuotientGroup.mk' (F n) g =
            inverseLimitProjection (cSQuotie.ofFiltration F hfin) n y) :
    Function.Bijective (filtrationCompletionMap F hfin)
  := by
  constructor
  · intro x y hxy
    have hsep : ∀ g : G, (∀ n, g ∈ F n) → g = 1 := by
      intro g hg
      have hgint : g ∈ filtrationIntersection F := hg
      have hbot : g ∈ (⊥ : Subgroup G) := by
        rw [← hseparated]
        exact hgint
      simpa using hbot
    have hmem : ∀ n, x * y⁻¹ ∈ F n := by
      intro n
      have hcoord := congrArg
        (fun z => inverseLimitProjection
          (cSQuotie.ofFiltration F hfin) n z)
        (show filtrationCompletionMap F hfin (x * y⁻¹) = 1 by
          rw [map_mul, map_inv, hxy, mul_inv_cancel])
      change QuotientGroup.mk' (F n) (x * y⁻¹) = 1 at hcoord
      exact (QuotientGroup.eq_one_iff (N := F n) (x * y⁻¹)).1 hcoord
    have hxy_one : x * y⁻¹ = 1 := hsep (x * y⁻¹) hmem
    exact mul_inv_eq_one.mp hxy_one
  · intro y
    rcases hcomplete y with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    ext n
    exact hg n
/-- The Nikolov-Segal automatic-continuity input for the local profinite API. -/
def AutomaticContinuityBridge {G : Type u} {H : Type v} [Group G] [Group H]
    {TG : pTopo G} {TH : pTopo H}
    (_FG : tFGenera G TG) : Prop :=
  ∀ φ : aHProfin G H TG TH,
    basicContinuous TG.topology TH.topology φ.hom
/-- Packaged continuous-lift form of automatic continuity. -/
def ContinuousLiftBridge {G : Type u} {H : Type v} [Group G] [Group H]
    {TG : pTopo G} {TH : pTopo H}
    (_FG : tFGenera G TG) : Prop :=
  ∀ φ : aHProfin G H TG TH,
    ∃ ψ : hPGroups G H TG TH, ψ.hom = φ.hom
/-- Finite continuous quotients detect density for the chosen generating set. -/
def ImagesDetectBridge {G : Type u} [Group G]
    {TG : pTopo G} (S : tGSet G TG) : Prop :=
  (∀ Q : fCQuota G TG,
      Subgroup.closure (Q.map '' S.carrier) = ⊤) ↔
    bDense TG.topology (S.denseGenerated.generated : Set G)
/-- Finite-index subgroups are open under the supplied Nikolov-Segal bridge. -/
def SubgroupsOpenBridge {G : Type u} [Group G]
    {TG : pTopo G} (_FG : tFGenera G TG) : Prop :=
  ∀ H : fISubgro G, TG.topology.IsOpen (H.subgroup : Set G)
/-- Abstract finite quotients have open kernels under the supplied automatic-continuity bridge. -/
def AbstractQuotientsBridge {G : Type u} [Group G]
    {TG : pTopo G} (_FG : tFGenera G TG) : Prop :=
  ∀ Q : aFQuot.{u, v} G, TG.topology.IsOpen (Q.kernel : Set G)
/-- Nikolov-Segal automatic continuity. -/
theorem nikolovSegalAutomatic {G : Type u} {H : Type v} [Group G] [Group H]
    {TG : pTopo G} {TH : pTopo H}
    (FG : tFGenera G TG)
    (hFI : SubgroupsOpenBridge FG)
    (φ : aHProfin G H TG TH) :
    basicContinuous TG.topology TH.topology φ.hom
  := by
  classical
  intro U hU
  let A : Set G := {g : G | φ.hom g ∈ U}
  let C : Set (Set G) := {V : Set G | TG.topology.IsOpen V ∧ V ⊆ A}
  have hAeq : A = ⋃₀ C := by
    ext x
    constructor
    · intro hxA
      rcases TH.exists_right_cosetsubset hU (show φ.hom x ∈ U from hxA) with
        ⟨N, _hNopen, hNsub, hNfinite⟩
      let K : nSubgro G := {
        carrier := N.carrier.comap φ.hom
        normal' := (show N.carrier.Normal from inferInstance).comap φ.hom
      }
      let q : G →* H ⧸ N.carrier := (QuotientGroup.mk' N.carrier).comp φ.hom
      have hker : K.carrier = MonoidHom.ker q := by
        ext g
        simp [K, q]
      have hKfinite : Finite (G ⧸ K.carrier) := by
        haveI : Finite (H ⧸ N.carrier) := hNfinite
        rw [hker]
        exact Finite.of_equiv q.range (QuotientGroup.quotientKerEquivRange q).symm
      have hKopen : TG.topology.IsOpen (K.carrier : Set G) :=
        hFI (fISubgro.ofNormal K hKfinite)
      let V : Set G := {y : G | x⁻¹ * y ∈ K.carrier}
      have hVopen : TG.topology.IsOpen V := by
        simpa [V] using
          TG.left_translate_continuous x⁻¹ (K.carrier : Set G) hKopen
      have hxV : x ∈ V := by
        simp [V, K]
      have hVsub : V ⊆ A := by
        intro y hy
        have hmem : φ.hom (x⁻¹ * y) ∈ N.carrier := by
          simpa [V, K] using hy
        have hycoset :
            φ.hom y ∈ {z : H | ∃ n ∈ (N.carrier : Set H), z = φ.hom x * n} := by
          refine ⟨φ.hom (x⁻¹ * y), hmem, ?_⟩
          rw [map_mul, map_inv]
          group
        exact hNsub hycoset
      exact ⟨V, by exact ⟨hVopen, hVsub⟩, hxV⟩
    · intro hx
      rcases hx with ⟨V, hVC, hxV⟩
      exact hVC.2 hxV
  rw [show {g : G | φ.hom g ∈ U} = A from rfl, hAeq]
  exact TG.topology.sUnion_open C (by
    intro V hVC
    exact hVC.1)
/-- Nikolov-Segal automatic-continuity theorem in packaged form. -/
theorem nikolovSegalContinuity {G : Type u} {H : Type v} [Group G] [Group H]
    {TG : pTopo G} {TH : pTopo H}
    (FG : tFGenera G TG)
    (hFI : SubgroupsOpenBridge FG)
    (φ : aHProfin G H TG TH) :
    ∃ ψ : hPGroups G H TG TH, ψ.hom = φ.hom
  := by
  have hcont := nikolovSegalAutomatic FG hFI φ
  refine ⟨{ φ with preimage_open_id := ?_, continuous' := hcont }, rfl⟩
  intro U hU _h1
  exact hcont U hU
/-- Finite-index subgroups are open under Nikolov-Segal hypotheses. -/
theorem nikolovSegalHypotheses {G : Type u} [Group G]
    {TG : pTopo G} (FG : tFGenera G TG)
    (hFI : SubgroupsOpenBridge FG)
    (H : fISubgro G) :
    TG.topology.IsOpen (H.subgroup : Set G)
  := by
  exact hFI H
/-- Automatic continuity turns abstract finite quotients into continuous quotients. -/
theorem automaticContinuityTurns {G : Type u}
    [Group G] {TG : pTopo G} (FG : tFGenera G TG)
    (hFI : SubgroupsOpenBridge FG)
    (Q : aFQuot G) :
    TG.topology.IsOpen (Q.kernel : Set G)
  := by
  classical
  rw [Q.kernel_eq]
  letI : Fintype Q.target := Fintype.ofFinite Q.target
  let TQ := pTopo.discreteOfFintype Q.target
  let φ : aHProfin G Q.target TG TQ := {
    hom := Q.map
  }
  have hcont : basicContinuous TG.topology (bTopo.discrete Q.target) Q.map := by
    simpa [TQ] using nikolovSegalAutomatic FG hFI φ
  exact openContinuousMaps Q.map hcont

end Theorems
end Submission
