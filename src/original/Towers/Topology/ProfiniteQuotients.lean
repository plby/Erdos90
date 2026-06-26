import Towers.Group.FilteredMaps
import Towers.Group.Zassenhaus

namespace Towers
namespace Topology

universe u v w
open Towers.Group

/-- Formal Hilbert-series algebra package, using the standard coefficient formulas. -/
structure fHAlg (R : Type u) [Semiring R] where
  add : (ℕ → R) → (ℕ → R) → (ℕ → R) := hilbertSeriesAdd
  mul : (ℕ → R) → (ℕ → R) → (ℕ → R) := hilbertSeriesMul
  zero : ℕ → R := fun _ => 0
  one : ℕ → R := fun n => if n = 0 then 1 else 0
  add_coeff : ∀ a b n, add a b n = a n + b n
  mul_coeff : ∀ a b n, mul a b n = Finset.sum (Finset.range (n + 1)) (fun i => a i * b (n - i))
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  zero_mul : ∀ a, mul zero a = zero
  mul_zero : ∀ a, mul a zero = zero
  mul_one : ∀ a, mul a one = a
  one_mul : ∀ a, mul one a = a

/-- Coefficient formula for addition in a formal Hilbert-series algebra. -/
theorem fHAlg.add_apply {R : Type u} [Semiring R]
    (A : fHAlg R) (a b : ℕ → R) (n : ℕ) :
    A.add a b n = a n + b n := A.add_coeff a b n

/-- Coefficient formula for multiplication in a formal Hilbert-series algebra. -/
theorem fHAlg.mul_apply {R : Type u} [Semiring R]
    (A : fHAlg R) (a b : ℕ → R) (n : ℕ) :
    A.mul a b n = Finset.sum (Finset.range (n + 1)) (fun i => a i * b (n - i)) :=
  A.mul_coeff a b n

/-- Data for a finite Hilbert-series cutoff check, optionally accompanied by a
tail certificate.  Without the tail certificate this records only what has been
verified up to `cutoff`, so the cutoff check is not made redundant by a global
inequality field. -/
structure hSArgume (R : Type u) [Semiring R] [Preorder R] where
  lhs : hilbertSeries R
  rhs : hilbertSeries R
  cutoff : ℕ
  verified_to_cutoff : ∀ n, n ≤ cutoff → lhs n ≤ rhs n
  tailCertificate : Type := PEmpty
  tail_bound : tailCertificate → ∀ n, cutoff < n → lhs n ≤ rhs n := by
    intro h
    cases h
  strictDegree : Option ℕ
  strict_witness : ∀ n, strictDegree = some n → n ≤ cutoff ∧ lhs n < rhs n


/-- The verified cutoff inequality, as a named projection. -/
theorem hSArgume.le_le_cutoff {R : Type u} [Semiring R] [Preorder R]
    (A : hSArgume R) {n : ℕ} (hn : n ≤ A.cutoff) :
    A.lhs n ≤ A.rhs n :=
  A.verified_to_cutoff n hn

/-- A Hilbert-series argument becomes globally coefficientwise once a tail
certificate is supplied. -/
theorem hSArgume.coeff_le_tailbound {R : Type u} [Semiring R] [Preorder R]
    (A : hSArgume R) (cert : A.tailCertificate) (n : ℕ) :
    A.lhs n ≤ A.rhs n := by
  by_cases hn : n ≤ A.cutoff
  · exact A.verified_to_cutoff n hn
  · exact A.tail_bound cert n (Nat.lt_of_not_ge hn)

/-- A strict-degree witness lies below the cutoff. -/
theorem hSArgume.strict_degree_lecutoff {R : Type u} [Semiring R] [Preorder R]
    (A : hSArgume R) {n : ℕ} (hn : A.strictDegree = some n) :
    n ≤ A.cutoff := (A.strict_witness n hn).1

/-- A strict-degree witness has a strict coefficient inequality. -/
theorem hSArgume.strictDegree_lt {R : Type u} [Semiring R] [Preorder R]
    (A : hSArgume R) {n : ℕ} (hn : A.strictDegree = some n) :
    A.lhs n < A.rhs n := (A.strict_witness n hn).2

/-- An open kernel in a lightweight profinite topology. -/
structure oKern {G : Type u} {H : Type v} [Group G] [Group H]
    (TG : pTopo G) (f : G →* H) where
  isOpen : TG.topology.IsOpen (MonoidHom.ker f : Set G)
  normal' : (MonoidHom.ker f).Normal := inferInstance
  quotient : Type u := G ⧸ MonoidHom.ker f
  quotientEquiv : quotient ≃ (G ⧸ MonoidHom.ker f)
  finiteQuotient : Finite quotient

attribute [instance] oKern.finiteQuotient

/-- The kernel in an open-kernel package is open. -/
theorem oKern.kernel_isOpen {G : Type u} {H : Type v} [Group G] [Group H]
    {TG : pTopo G} {f : G →* H} (K : oKern TG f) :
    TG.topology.IsOpen (MonoidHom.ker f : Set G) := K.isOpen

/-- An open kernel is closed in the lightweight profinite sense (open complement). -/
theorem oKern.kernel_compl_opena {G : Type u} {H : Type v} [Group G] [Group H]
    {TG : pTopo G} {f : G →* H} (K : oKern TG f) :
    TG.topology.IsOpen ((MonoidHom.ker f : Set G)ᶜ) :=
  TG.open_compl_opensubgroup (MonoidHom.ker f) K.isOpen

/-- Build a continuous homomorphism from a continuous map whose kernel is open.
Open subgroups are closed in the lightweight profinite topology, so the closed-kernel
field is derived rather than supplied independently. -/
def cHom.ofOpenKernel {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : G →* H) (hf : basicContinuous TG.topology TH.topology f)
    (K : oKern TG f) : cHom G H TG TH where
  hom := f
  continuous' := hf
  kernel_closed := K.kernel_compl_opena

@[simp] theorem cHom.open_kernel_hom {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : G →* H) (hf : basicContinuous TG.topology TH.topology f)
    (K : oKern TG f) :
    (cHom.ofOpenKernel f hf K).hom = f := rfl

/-- The recorded quotient type is identified with the actual kernel quotient. -/
def oKern.quotient_equiv {G : Type u} {H : Type v} [Group G] [Group H]
    {TG : pTopo G} {f : G →* H} (K : oKern TG f) :
    K.quotient ≃ (G ⧸ MonoidHom.ker f) := K.quotientEquiv

/-- The quotient type in an open-kernel package is finite. -/
theorem oKern.quotient_finite {G : Type u} {H : Type v} [Group G] [Group H]
    {TG : pTopo G} {f : G →* H} (K : oKern TG f) :
    Finite K.quotient :=
  K.finiteQuotient

/-- The quotient projection attached to an open normal subgroup has open kernel. -/
noncomputable def oNSubgro.toOpenKernel {G : Type u} [Group G]
    {T : pTopo G} (N : oNSubgro G T) :
    oKern T N.normal.projection where
  isOpen := by
    simpa [N.normal.ker_projection] using N.isOpen'
  quotient := quotientGroup N.normal
  quotientEquiv :=
    (QuotientGroup.quotientMulEquivOfEq N.normal.ker_projection.symm).toEquiv
  finiteQuotient := N.finiteQuotient


/-- A finite continuous quotient map. -/
structure fCQuota (G : Type u) [Group G] (TG : pTopo G) where
  target : Type u
  [group_target : Group target]
  [finite_target : Finite target]
  targetTopology : bTopo target
  target_discrete : ∀ U : Set target, targetTopology.IsOpen U
  map : G →* target
  surjective : Function.Surjective map
  continuous' : basicContinuous TG.topology targetTopology map
  open_map : basicOpenMap TG.topology targetTopology map
  kernelOpen : TG.topology.IsOpen (MonoidHom.ker map : Set G)
  kernelNormal : (MonoidHom.ker map).Normal := inferInstance

attribute [instance] fCQuota.group_target fCQuota.finite_target


/-- Build a finite continuous quotient with the discrete topology on the finite target.
Here continuity is exactly openness of all fibers/preimages; openness of the quotient map
and openness of the kernel are then derived, not supplied independently. -/
noncomputable def fCQuota.ofDiscreteTarget {G : Type u} [Group G]
    (TG : pTopo G) (A : Type u) [Group A] [Finite A]
    (f : G →* A) (hsurj : Function.Surjective f)
    (hpre : ∀ U : Set A, TG.topology.IsOpen (f ⁻¹' U)) :
    fCQuota G TG where
  target := A
  group_target := inferInstance
  finite_target := inferInstance
  targetTopology := bTopo.discrete A
  target_discrete := by intro U; trivial
  map := f
  surjective := hsurj
  continuous' := by intro U hU; exact hpre U
  open_map := bTopo.open_to_discrete TG.topology f
  kernelOpen := by
    simpa [MonoidHom.mem_ker] using hpre ({1} : Set A)

@[simp] theorem fCQuota.discrete_target_map {G : Type u} [Group G]
    (TG : pTopo G) (A : Type u) [Group A] [Finite A]
    (f : G →* A) (hsurj : Function.Surjective f)
    (hpre : ∀ U : Set A, TG.topology.IsOpen (f ⁻¹' U)) :
    (fCQuota.ofDiscreteTarget TG A f hsurj hpre).map = f := rfl

/-- The map of a finite continuous quotient is surjective. -/
theorem fCQuota.map_surjective {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    Function.Surjective Q.map := Q.surjective

/-- Every subset of the finite target is open in its recorded discrete topology. -/
theorem fCQuota.target_isOpen {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) (U : Set Q.target) :
    Q.targetTopology.IsOpen U := Q.target_discrete U

/-- Preimages of target-open sets are open. -/
theorem fCQuota.preimage_isOpen {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG)
    {U : Set Q.target} (hU : Q.targetTopology.IsOpen U) :
    TG.topology.IsOpen (Q.map ⁻¹' U) := Q.continuous' U hU

/-- Images of open sets are open under the recorded open map. -/
theorem fCQuota.image_isOpen {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG)
    {U : Set G} (hU : TG.topology.IsOpen U) :
    Q.targetTopology.IsOpen (Q.map '' U) := Q.open_map U hU

/-- The kernel of a finite continuous quotient is open. -/
theorem fCQuota.kernel_isOpen {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    TG.topology.IsOpen (MonoidHom.ker Q.map : Set G) :=
  Q.kernelOpen


/-- A finite continuous quotient has an open kernel; the quotient type is identified
with the actual kernel quotient by the first isomorphism theorem. -/
noncomputable def fCQuota.toOpenKernel {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    oKern TG Q.map where
  isOpen := Q.kernelOpen
  quotient := Q.target
  quotientEquiv :=
    (QuotientGroup.quotientKerEquivOfSurjective (φ := Q.map) Q.surjective).toEquiv.symm
  finiteQuotient := Q.finite_target

@[simp] theorem fCQuota.open_kernel_open {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    (Q.toOpenKernel).isOpen = Q.kernelOpen := rfl


/-- View a finite continuous quotient as a continuous homomorphism into any profinite
topology on the target whose open sets are also open for the quotient topology. -/
noncomputable def fCQuota.toContinuousHomomorphism {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG)
    (TH : pTopo Q.target)
    (hopen : ∀ U : Set Q.target, TH.topology.IsOpen U → Q.targetTopology.IsOpen U) :
    cHom G Q.target TG TH where
  hom := Q.map
  continuous' := by intro U hU; exact Q.continuous' U (hopen U hU)
  kernel_closed := Q.toOpenKernel.kernel_compl_opena

/-- If two target lightweight topologies have the same opens, a finite continuous quotient
is a continuous-open homomorphism into the supplied profinite target topology. -/
noncomputable def fCQuota.cont_open_maps {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG)
    (TH : pTopo Q.target)
    (h₁ : ∀ U : Set Q.target, TH.topology.IsOpen U → Q.targetTopology.IsOpen U)
    (h₂ : ∀ U : Set Q.target, Q.targetTopology.IsOpen U → TH.topology.IsOpen U) :
    cOMaps G Q.target TG TH where
  hom := Q.map
  continuous' := by intro U hU; exact Q.continuous' U (h₁ U hU)
  open' := by intro U hU; exact h₂ (Q.map '' U) (Q.open_map U hU)
  kernel_closed := Q.toOpenKernel.kernel_compl_opena


/-- The canonical discrete profinite topology on the finite target of a quotient. -/
noncomputable def fCQuota.discreteTargetTopology {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    pTopo Q.target := by
  classical
  letI : Fintype Q.target := Fintype.ofFinite Q.target
  exact pTopo.discreteOfFintype Q.target

/-- A finite continuous quotient is canonically a continuous-open map into its finite
target equipped with the discrete profinite topology. -/
noncomputable def fCQuota.discrete_cont_openmaps {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    cOMaps G Q.target TG Q.discreteTargetTopology := by
  classical
  refine Q.cont_open_maps Q.discreteTargetTopology ?_ ?_
  · intro U hU
    exact Q.target_discrete U
  · intro U hU
    dsimp [fCQuota.discreteTargetTopology, pTopo.discreteOfFintype]
    trivial

@[simp] theorem fCQuota.discrete_contopen_mapshom {G : Type u}
    [Group G] {TG : pTopo G} (Q : fCQuota G TG) :
    (Q.discrete_cont_openmaps).hom = Q.map := rfl

/-- The recorded map of a finite continuous quotient is continuous. -/
theorem fCQuota.continuous {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    basicContinuous TG.topology Q.targetTopology Q.map :=
  Q.continuous'

/-- The recorded map of a finite continuous quotient is open. -/
theorem fCQuota.is_open_map {G : Type u} [Group G]
    {TG : pTopo G} (Q : fCQuota G TG) :
    basicOpenMap TG.topology Q.targetTopology Q.map :=
  Q.open_map

/-- A closed normal subgroup, using a lightweight closed predicate. -/
structure cNSubgro (G : Type u) [Group G] (T : pTopo G) where
  subgroup : Subgroup G
  normal' : subgroup.Normal
  isClosed : T.topology.IsOpen ((subgroup : Set G)ᶜ)
  conjugation_closed : ∀ {x : G}, x ∈ subgroup → ∀ g : G, g * x * g⁻¹ ∈ subgroup
  separates_outside : ∀ x : G, x ∉ subgroup → ∃ U : Set G,
    T.topology.IsOpen U ∧ x ∈ U ∧ Disjoint U (subgroup : Set G)

attribute [instance] cNSubgro.normal'

/-- A closed normal subgroup is closed in the lightweight sense. -/
theorem cNSubgro.closed_open_compl {G : Type u} [Group G]
    {T : pTopo G} (N : cNSubgro G T) :
    T.topology.IsOpen ((N.subgroup : Set G)ᶜ) := N.isClosed

/-- Conjugation preserves membership in a closed normal subgroup. -/
theorem cNSubgro.conj_mem {G : Type u} [Group G]
    {T : pTopo G} (N : cNSubgro G T)
    {x : G} (hx : x ∈ N.subgroup) (g : G) : g * x * g⁻¹ ∈ N.subgroup :=
  N.conjugation_closed hx g

/-- Points outside a closed normal subgroup have a separating open neighborhood. -/
theorem cNSubgro.exists_opendisjoint_notmem {G : Type u} [Group G]
    {T : pTopo G} (N : cNSubgro G T) {x : G}
    (hx : x ∉ N.subgroup) : ∃ U : Set G,
      T.topology.IsOpen U ∧ x ∈ U ∧ Disjoint U (N.subgroup : Set G) :=
  N.separates_outside x hx

/-- Forget a closed normal subgroup to the algebraic normal-subgroup package. -/
def cNSubgro.toNormalSubgroup {G : Type u} [Group G] {T : pTopo G}
    (N : cNSubgro G T) : nSubgro G where
  carrier := N.subgroup
  normal' := N.normal'

/-- The quotient projection associated to a closed normal subgroup. -/
def cNSubgro.projection {G : Type u} [Group G] {T : pTopo G}
    (N : cNSubgro G T) : G →* quotientGroup N.toNormalSubgroup :=
  N.toNormalSubgroup.projection

@[simp] theorem cNSubgro.mem_normal_subgroup {G : Type u} [Group G]
    {T : pTopo G} (N : cNSubgro G T) (g : G) :
    g ∈ N.toNormalSubgroup.carrier ↔ g ∈ N.subgroup := Iff.rfl

/-- The quotient projection of a closed normal subgroup is surjective. -/
theorem cNSubgro.projection_surjective {G : Type u} [Group G]
    {T : pTopo G} (N : cNSubgro G T) :
    Function.Surjective N.projection :=
  N.toNormalSubgroup.projection_surjective

/-- The kernel of the quotient projection is the closed normal subgroup. -/
theorem cNSubgro.kernel_projection {G : Type u} [Group G]
    {T : pTopo G} (N : cNSubgro G T) :
    MonoidHom.ker N.projection = N.subgroup :=
  N.toNormalSubgroup.ker_projection


/-- An abstract homomorphism between profinite groups: just the underlying group
homomorphism, with no continuity assumption.  Continuous variants are packaged
separately so automatic-continuity statements can use this as their input. -/
structure aHProfin (G : Type u) (H : Type v)
    [Group G] [Group H] (TG : pTopo G) (TH : pTopo H) where
  hom : G →* H
  map_one : hom (1 : G) = 1 := hom.map_one
  map_mul : ∀ x y : G, hom (x * y) = hom x * hom y := hom.map_mul

/-- A continuous abstract profinite homomorphism, keeping continuity data
separate from the raw abstract homomorphism. -/
structure hPGroups (G : Type u) (H : Type v)
    [Group G] [Group H] (TG : pTopo G) (TH : pTopo H) extends
    aHProfin G H TG TH where
  preimage_open_id : ∀ U : Set H, TH.topology.IsOpen U → (1 : H) ∈ U →
    TG.topology.IsOpen {g : G | hom g ∈ U}
  continuous' : basicContinuous TG.topology TH.topology hom

/-- A continuous homomorphism gives an abstract profinite homomorphism by forgetting
all continuity and closed-kernel data. -/
def cHom.toAbstract {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cHom G H TG TH) :
    aHProfin G H TG TH where
  hom := f.hom

/-- A continuous homomorphism as a continuous abstract profinite homomorphism. -/
def cHom.toContinuousAbstract {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cHom G H TG TH) :
    hPGroups G H TG TH where
  hom := f.hom
  preimage_open_id := by
    intro U hU _
    exact f.continuous' U hU
  continuous' := f.continuous'

@[simp] theorem cHom.toAbstract_hom {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (f : cHom G H TG TH) : f.toAbstract.hom = f.hom := rfl

/-- Identity abstract profinite homomorphism. -/
def aHProfin.id (G : Type u) [Group G]
    (TG : pTopo G) : aHProfin G G TG TG where
  hom := MonoidHom.id G

/-- Composition of abstract profinite homomorphisms. -/
def aHProfin.comp {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (β : aHProfin H K TH TK)
    (α : aHProfin G H TG TH) :
    aHProfin G K TG TK where
  hom := β.hom.comp α.hom

/-- Identity continuous abstract profinite homomorphism. -/
def hPGroups.id (G : Type u) [Group G]
    (TG : pTopo G) : hPGroups G G TG TG where
  hom := MonoidHom.id G
  preimage_open_id := by intro U hU _; simpa using hU
  continuous' := basicContinuous_id TG.topology

/-- Composition of continuous abstract profinite homomorphisms. -/
def hPGroups.comp {G : Type u} {H : Type v} {K : Type w}
    [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (β : hPGroups H K TH TK)
    (α : hPGroups G H TG TH) :
    hPGroups G K TG TK where
  hom := β.hom.comp α.hom
  preimage_open_id := by
    intro U hU h1
    let V : Set H := {h | β.hom h ∈ U}
    have hVopen : TH.topology.IsOpen V := β.preimage_open_id U hU h1
    have hVone : (1 : H) ∈ V := by simp [V, β.map_one, h1]
    simpa [V, MonoidHom.comp_apply] using α.preimage_open_id V hVopen hVone
  continuous' :=
    basicContinuous_comp TG.topology TH.topology TK.topology
      α.continuous' β.continuous'

/-- The recorded homomorphism of a continuous abstract profinite homomorphism is continuous. -/
theorem hPGroups.continuous {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (φ : hPGroups G H TG TH) :
    basicContinuous TG.topology TH.topology φ.hom :=
  φ.continuous'

/-- Neighborhood-of-identity continuity test, as a named accessor. -/
theorem hPGroups.preimage_open_id' {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (φ : hPGroups G H TG TH) {U : Set H}
    (hU : TH.topology.IsOpen U) (h1 : (1 : H) ∈ U) :
    TG.topology.IsOpen {g : G | φ.hom g ∈ U} :=
  φ.preimage_open_id U hU h1

@[simp] theorem aHProfin.map_one_apply {G : Type u} {H : Type v}
    [Group G] [Group H] {TG : pTopo G} {TH : pTopo H}
    (φ : aHProfin G H TG TH) : φ.hom (1 : G) = 1 :=
  φ.map_one

@[simp] theorem aHProfin.id_hom (G : Type u) [Group G]
    (TG : pTopo G) :
    (aHProfin.id G TG).hom = MonoidHom.id G := rfl

@[simp] theorem hPGroups.id_hom
    (G : Type u) [Group G] (TG : pTopo G) :
    (hPGroups.id G TG).hom = MonoidHom.id G := rfl

@[simp] theorem aHProfin.comp_hom {G : Type u} {H : Type v}
    {K : Type w} [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (β : aHProfin H K TH TK)
    (α : aHProfin G H TG TH) :
    (β.comp α).hom = β.hom.comp α.hom := rfl

@[simp] theorem hPGroups.comp_hom
    {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (β : hPGroups H K TH TK)
    (α : hPGroups G H TG TH) :
    (β.comp α).hom = β.hom.comp α.hom := rfl

@[simp] theorem aHProfin.comp_apply {G : Type u} {H : Type v}
    {K : Type w} [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (β : aHProfin H K TH TK)
    (α : aHProfin G H TG TH) (g : G) :
    (β.comp α).hom g = β.hom (α.hom g) := rfl

@[simp] theorem hPGroups.comp_apply
    {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]
    {TG : pTopo G} {TH : pTopo H} {TK : pTopo K}
    (β : hPGroups H K TH TK)
    (α : hPGroups G H TG TH) (g : G) :
    (β.comp α).hom g = β.hom (α.hom g) := rfl

/-- A quotient map in the profinite setting, exposing its kernel and the
universal factorization property for maps killing that kernel. -/
structure pQMap (G : Type u) [Group G] (TG : pTopo G) where
  quotient : fCQuota G TG
  kernel : nSubgro G := ⟨MonoidHom.ker quotient.map, inferInstance⟩
  kernel_eq : kernel.carrier = MonoidHom.ker quotient.map
  open_kernel : TG.topology.IsOpen (kernel.carrier : Set G)
  factor_lift : ∀ {K : Type u} [Group K] (f : G →* K),
    kernel.carrier ≤ MonoidHom.ker f → quotient.target →* K
  factor_comm : ∀ {K : Type u} [Group K] (f : G →* K) (hker),
    (factor_lift f hker).comp quotient.map = f
  factor_unique : ∀ {K : Type u} [Group K] (f : G →* K) (hker)
    (ψ : quotient.target →* K), ψ.comp quotient.map = f → ψ = factor_lift f hker

/-- The kernel of a profinite quotient map is open. -/
theorem pQMap.kernel_isOpen {G : Type u} [Group G]
    {TG : pTopo G} (Q : pQMap G TG) :
    TG.topology.IsOpen (Q.kernel.carrier : Set G) := Q.open_kernel


/-- The actual kernel of the underlying quotient map is open (not just the packaged copy). -/
theorem pQMap.actual_kernel_open {G : Type u} [Group G]
    {TG : pTopo G} (Q : pQMap G TG) :
    TG.topology.IsOpen (MonoidHom.ker Q.quotient.map : Set G) := by
  simpa [Q.kernel_eq] using Q.open_kernel

/-- Forget a profinite quotient map to its open-kernel package. -/
noncomputable def pQMap.toOpenKernel {G : Type u} [Group G]
    {TG : pTopo G} (Q : pQMap G TG) :
    oKern TG Q.quotient.map :=
  Q.quotient.toOpenKernel

/-- The underlying finite quotient map is surjective. -/
theorem pQMap.quotient_surjective {G : Type u} [Group G]
    {TG : pTopo G} (Q : pQMap G TG) :
    Function.Surjective Q.quotient.map := Q.quotient.surjective

/-- Pointwise form of the universal factorization commutative square. -/
theorem pQMap.factor_comm_apply {G : Type u} [Group G]
    {TG : pTopo G} (Q : pQMap G TG)
    {K : Type u} [Group K] (f : G →* K) (hker) (g : G) :
    Q.factor_lift f hker (Q.quotient.map g) = f g := by
  have h := Q.factor_comm f hker
  exact congrArg (fun φ : G →* K => φ g) h

/-- The universal factorization through a profinite quotient is unique. -/
theorem pQMap.factor_unique' {G : Type u} [Group G]
    {TG : pTopo G} (Q : pQMap G TG)
    {K : Type u} [Group K] (f : G →* K) (hker)
    (ψ : Q.quotient.target →* K) (hψ : ψ.comp Q.quotient.map = f) :
    ψ = Q.factor_lift f hker :=
  Q.factor_unique f hker ψ hψ

/-- The factor lift commutes with the quotient map. -/
theorem pQMap.factor_comm' {G : Type u} [Group G]
    {TG : pTopo G} (Q : pQMap G TG)
    {K : Type u} [Group K] (f : G →* K) (hker) :
    (Q.factor_lift f hker).comp Q.quotient.map = f :=
  Q.factor_comm f hker

/-- Compatible filtration quotients across degrees. -/
structure cFQuotie (G : Type u) [Group G] where
  quotient : ℕ → nSubgro G
  antitone : ∀ {m n : ℕ}, m ≤ n → (quotient n).carrier ≤ (quotient m).carrier
  transition :
    ∀ {m n : ℕ},
      m ≤ n → quotientGroup (quotient n) →* quotientGroup (quotient m)
  transition_surjective : ∀ {m n : ℕ} (h : m ≤ n), Function.Surjective (transition h)
  transition_id : ∀ n, transition (Nat.le_refl n) = MonoidHom.id (quotientGroup (quotient n))
  transition_comp : ∀ {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n),
    (transition hkm).comp (transition hmn) = transition (Nat.le_trans hkm hmn)
  projection : ∀ n, G →* quotientGroup (quotient n) := fun n =>
    QuotientGroup.mk' (quotient n).carrier
  projection_compat : ∀ {m n : ℕ} (h : m ≤ n),
    (transition h).comp (projection n) = projection m
  projection_kernel : ∀ n, MonoidHom.ker (projection n) = (quotient n).carrier


/-- The transition maps in a compatible system are surjective. -/
theorem cFQuotie.transition_surj {G : Type u} [Group G]
    (Q : cFQuotie G) {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (Q.transition h) := Q.transition_surjective h

/-- The quotient subgroups are antitone in the index. -/
theorem cFQuotie.subset_of_le {G : Type u} [Group G]
    (Q : cFQuotie G) {m n : ℕ} (h : m ≤ n) :
    (Q.quotient n).carrier ≤ (Q.quotient m).carrier := Q.antitone h

/-- Identity transition, named for rewriting. -/
@[simp] theorem cFQuotie.transition_self {G : Type u} [Group G]
    (Q : cFQuotie G) (n : ℕ) :
    Q.transition (Nat.le_refl n) = MonoidHom.id (quotientGroup (Q.quotient n)) :=
  Q.transition_id n

/-- Pointwise compatibility of projections in compatible filtration quotients. -/
theorem cFQuotie.projection_compat_apply {G : Type u} [Group G]
    (Q : cFQuotie G) {m n : ℕ} (h : m ≤ n) (g : G) :
    Q.transition h (Q.projection n g) = Q.projection m g := by
  have H := Q.projection_compat h
  exact congrArg (fun f : G →* quotientGroup (Q.quotient m) => f g) H

/-- Membership in a quotient term is equivalently vanishing under its projection. -/
theorem cFQuotie.memquot_iffprojection_eqone
    {G : Type u} [Group G] (Q : cFQuotie G) (n : ℕ) (g : G) :
    g ∈ (Q.quotient n).carrier ↔ Q.projection n g = 1 := by
  have h := congrArg (fun S : Subgroup G => g ∈ S) (Q.projection_kernel n)
  change (g ∈ MonoidHom.ker (Q.projection n)) = (g ∈ (Q.quotient n).carrier) at h
  rw [← h]
  rfl

/-- Pointwise form of transition composition in compatible filtration quotients. -/
theorem cFQuotie.transition_comp_apply {G : Type u} [Group G]
    (Q : cFQuotie G) {k m n : ℕ}
    (hkm : k ≤ m) (hmn : m ≤ n) (x : quotientGroup (Q.quotient n)) :
    Q.transition hkm (Q.transition hmn x) =
      Q.transition (Nat.le_trans hkm hmn) x := by
  have h := Q.transition_comp hkm hmn
  exact congrArg (fun f : quotientGroup (Q.quotient n) →* quotientGroup (Q.quotient k) => f x) h

/-- Kernel equality for a compatible quotient projection, as a named accessor. -/
theorem cFQuotie.projection_kernel_eq {G : Type u} [Group G]
    (Q : cFQuotie G) (n : ℕ) :
    MonoidHom.ker (Q.projection n) = (Q.quotient n).carrier :=
  Q.projection_kernel n


end Topology
end Towers

/-!
## Statements migrated from `Towers.Theorems`

These declarations keep their historical `Towers.Theorems` namespace while living
next to the API they describe.
-/

namespace Towers
namespace Theorems

open Towers.Group
open Towers.Algebra
open Towers.Topology

universe u v w x

/-- An open normal subgroup gives a finite quotient. -/
theorem openNormalGives {G : Type u} [Group G]
    {T : pTopo G} (N : nSubgro G)
    (hopen : T.topology.IsOpen (N.carrier : Set G)) :
    Finite (quotientGroup N)
  := by
  rcases T.openNormalBasis (N.carrier : Set G) hopen N.carrier.one_mem with
    ⟨K, _hKopen, hKN, hKfin⟩
  exact Finite.of_surjective (quotientMapLE K N hKN) (of_le_surjective K N hKN)
/-- Finite continuous quotient kernels are open. -/
theorem openContinuousMaps {G : Type u} {Q : Type v}
    [Group G] [Group Q] [Finite Q] {TG : pTopo G}
    (φ : G →* Q) (hcont : basicContinuous TG.topology (bTopo.discrete Q) φ) :
    TG.topology.IsOpen (MonoidHom.ker φ : Set G)
  := by
  simpa [MonoidHom.mem_ker] using hcont ({1} : Set Q) (by trivial)

/-- Relevant kernels are open. -/
theorem kernelOpenness {G : Type u} {H : Type v} [Group G] [Group H] [Finite H]
    {TG : pTopo G} (φ : G →* H)
    (hcont : basicContinuous TG.topology (bTopo.discrete H) φ) :
    TG.topology.IsOpen (MonoidHom.ker φ : Set G)
  := by
  exact openContinuousMaps φ hcont

/-- Finite images detect topological generation. -/
theorem imagesDetectGeneration {G : Type u} [Group G]
    {TG : pTopo G} (S : Set G) :
    (∀ Q : fCQuota G TG,
      Subgroup.closure (Q.map '' S) = ⊤) ↔
      bDense TG.topology (Subgroup.closure S : Set G)
  := by
  classical
  constructor
  · intro hfinite U hU hUne
    rcases hUne with ⟨g, hgU⟩
    rcases TG.exists_right_cosetsubset (U := U) hU hgU with
      ⟨N, hNopen, hcoset, hNfinite⟩
    let π : G →* quotientGroup N := N.projection
    have hpre : ∀ A : Set (quotientGroup N), TG.topology.IsOpen (π ⁻¹' A) := by
      intro A
      let C : Set (Set G) :=
        {V | ∃ q : quotientGroup N, q ∈ A ∧ V = π ⁻¹' ({q} : Set (quotientGroup N))}
      have hfiber : ∀ q : quotientGroup N,
          TG.topology.IsOpen (π ⁻¹' ({q} : Set (quotientGroup N))) := by
        intro q
        rcases N.projection_surjective q with ⟨a, rfl⟩
        have hopenRight :
            TG.topology.IsOpen {y : G | y * a ∈ (N.carrier : Set G)} :=
          TG.right_translate_continuous a (N.carrier : Set G) hNopen
        have hopenInv :
            TG.topology.IsOpen {x : G | x⁻¹ * a ∈ (N.carrier : Set G)} :=
          TG.inv_continuous {y : G | y * a ∈ (N.carrier : Set G)} hopenRight
        have hset :
            π ⁻¹' ({π a} : Set (quotientGroup N)) =
              {x : G | x⁻¹ * a ∈ (N.carrier : Set G)} := by
          ext x
          change π x ∈ ({π a} : Set (quotientGroup N)) ↔
            x⁻¹ * a ∈ (N.carrier : Set G)
          rw [Set.mem_singleton_iff]
          exact QuotientGroup.eq
        simpa [hset, π] using hopenInv
      have hCopen : ∀ V ∈ C, TG.topology.IsOpen V := by
        intro V hV
        rcases hV with ⟨q, _hqA, rfl⟩
        exact hfiber q
      have hpre_eq : π ⁻¹' A = ⋃₀ C := by
        ext x
        constructor
        · intro hx
          refine ⟨π ⁻¹' ({π x} : Set (quotientGroup N)), ?_, ?_⟩
          · exact ⟨π x, hx, rfl⟩
          · simp
        · intro hx
          rcases hx with ⟨V, hVC, hxV⟩
          rcases hVC with ⟨q, hqA, rfl⟩
          have hxq : π x = q := by
            simpa [Set.mem_singleton_iff] using hxV
          simpa [hxq] using hqA
      rw [hpre_eq]
      exact TG.topology.sUnion_open C hCopen
    let Q : fCQuota G TG :=
      fCQuota.ofDiscreteTarget TG (quotientGroup N) π
        N.projection_surjective hpre
    have hqmem : π g ∈ Subgroup.closure (π '' S) := by
      have htop : Subgroup.closure (Q.map '' S) = ⊤ := hfinite Q
      have : Q.map g ∈ Subgroup.closure (Q.map '' S) := by
        rw [htop]
        exact Subgroup.mem_top _
      simpa [Q, π] using this
    rw [← MonoidHom.map_closure π S] at hqmem
    rcases Subgroup.mem_map.mp hqmem with ⟨x, hxS, hxπ⟩
    refine ⟨x, ?_, hxS⟩
    apply hcoset
    have hxg : x⁻¹ * g ∈ N.carrier := by
      exact (QuotientGroup.eq.mp (by simpa [π, nSubgro.projection] using hxπ))
    have hgx : g⁻¹ * x ∈ N.carrier := by
      have h := N.carrier.inv_mem hxg
      simpa [mul_inv_rev] using h
    refine ⟨g⁻¹ * x, hgx, ?_⟩
    group
  · intro hdense Q
    apply eq_top_iff.mpr
    intro q _hq
    rcases Q.surjective q with ⟨g, hg⟩
    have hopen : TG.topology.IsOpen (Q.map ⁻¹' ({q} : Set Q.target)) :=
      Q.preimage_isOpen (Q.target_isOpen ({q} : Set Q.target))
    have hne : (Q.map ⁻¹' ({q} : Set Q.target)).Nonempty := by
      refine ⟨g, ?_⟩
      simp [hg]
    rcases hdense (Q.map ⁻¹' ({q} : Set Q.target)) hopen hne with
      ⟨x, hxq, hxS⟩
    have hxmap : Q.map x = q := by
      simpa [Set.mem_singleton_iff] using hxq
    have hxmem : Q.map x ∈ Subgroup.closure (Q.map '' S) := by
      have hmap : Q.map x ∈ (Subgroup.closure S).map Q.map :=
        Subgroup.mem_map_of_mem Q.map hxS
      simpa [MonoidHom.map_closure] using hmap
    simpa [hxmap] using hxmem
/-- Open subgroups of profinite groups have finite index. -/
theorem openProfiniteGroup {G : Type u} [Group G]
    {TG : pTopo G} (N : nSubgro G)
    (hopen : TG.topology.IsOpen (N.carrier : Set G)) :
    Finite (G ⧸ N.carrier)
  := by
  exact openNormalGives N hopen

/-- Jennings-style openness input for filtration terms.

A filtration term is open once it contains an open normal neighborhood of the
identity.  Openness of Zassenhaus terms themselves is not automatic from the
bare group-theoretic definition. -/
theorem styleOpennessInputs {G : Type u} [Group G]
    {TG : pTopo G} {p n : ℕ}
    (hbasis : ∃ N : oNSubgro G TG,
      (N.normal.carrier : Set G) ⊆ GroupAlgebra.zSubgro p G n) :
    TG.topology.IsOpen (GroupAlgebra.zSubgro p G n : Set G)
  := by
  rcases hbasis with ⟨N, hNle⟩
  let H : Subgroup G := GroupAlgebra.zSubgro p G n
  let U : H → Set G := fun h => {x : G | h.1⁻¹ * x ∈ N.normal.carrier}
  have hU : ∀ h : H, TG.topology.IsOpen (U h) := by
    intro h
    exact TG.left_translate_continuous h.1⁻¹ (N.normal.carrier : Set G) N.isOpen'
  have hcover : (H : Set G) = ⋃ h : H, U h := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      simp [U]
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨h, hh⟩
      have hN_in_H : h.1⁻¹ * x ∈ H := hNle hh
      have hprod : h.1 * (h.1⁻¹ * x) ∈ H := H.mul_mem h.2 hN_in_H
      simpa [mul_assoc] using hprod
  rw [hcover]
  exact TG.topology.iUnion_open U hU
/-- Open filtration terms yield finite layers. -/
theorem openYieldLayers {G : Type u} [Group G]
    {TG : pTopo G} (F : DFilt G) (n : ℕ)
    (hopen : TG.topology.IsOpen (F n : Set G)) :
    Finite (G ⧸ F n)
  := by
  exact openProfiniteGroup (filtrationNormalTerm F n) hopen

end Theorems
end Towers
