import Submission.Topology.ProfiniteQuotients

namespace Submission
namespace Algebra

universe u v w w'
open Submission.Group

/-- A filtered algebra, represented by degree-indexed `R`-submodules whose
products respect degree. -/
structure fAlg (R : Type u) [CommSemiring R] where
  A : Type v
  [semiringA : Semiring A]
  [algebraA : Algebra R A]
  filtration : ℕ → Submodule R A
  one_mem_zero : (1 : A) ∈ filtration 0
  mul_mem :
    ∀ m n {x y : A},
      x ∈ filtration m → y ∈ filtration n → x * y ∈ filtration (m + n)
  /-- Each filtration term is stable under left multiplication by arbitrary algebra elements. -/
  left_mul_mem : ∀ n (a : A) {x : A}, x ∈ filtration n → a * x ∈ filtration n
  /-- Each filtration term is stable under right multiplication by arbitrary algebra elements. -/
  right_mul_mem : ∀ n (a : A) {x : A}, x ∈ filtration n → x * a ∈ filtration n
  antitone : ∀ {m n}, m ≤ n → filtration n ≤ filtration m
  exhaustive_zero : filtration 0 = ⊤

attribute [instance] fAlg.semiringA fAlg.algebraA

/-- Every element lies in degree zero of an exhaustive filtered algebra. -/
theorem fAlg.mem_zero {R : Type u} [CommSemiring R]
    (F : fAlg R) (x : F.A) : x ∈ F.filtration 0 := by
  rw [F.exhaustive_zero]
  exact trivial

/-- Pointwise antitonicity for filtered algebra terms. -/
theorem fAlg.mem_of_le {R : Type u} [CommSemiring R]
    (F : fAlg R) {m n : ℕ} (h : m ≤ n) {x : F.A}
    (hx : x ∈ F.filtration n) : x ∈ F.filtration m :=
  F.antitone h hx

/-- Left ideal stability of a filtration term. -/
theorem fAlg.left_mul_mem' {R : Type u} [CommSemiring R]
    (F : fAlg R) {n : ℕ} (a : F.A) {x : F.A}
    (hx : x ∈ F.filtration n) : a * x ∈ F.filtration n :=
  F.left_mul_mem n a hx

/-- Right ideal stability of a filtration term. -/
theorem fAlg.right_mul_mem' {R : Type u} [CommSemiring R]
    (F : fAlg R) {n : ℕ} (a : F.A) {x : F.A}
    (hx : x ∈ F.filtration n) : x * a ∈ F.filtration n :=
  F.right_mul_mem n a hx

/-- Named multiplication closure for filtered algebra elements. -/
theorem fAlg.mul_mem' {R : Type u} [CommSemiring R]
    (F : fAlg R) {m n : ℕ} {x y : F.A}
    (hx : x ∈ F.filtration m) (hy : y ∈ F.filtration n) :
    x * y ∈ F.filtration (m + n) :=
  F.mul_mem m n hx hy


/-- The unit lies in degree zero of a filtered algebra. -/
theorem fAlg.one_mem_zero' {R : Type u} [CommSemiring R]
    (F : fAlg R) : (1 : F.A) ∈ F.filtration 0 :=
  F.one_mem_zero

/-- The zeroth term of a filtered algebra is the whole algebra. -/
@[simp] theorem fAlg.filt_zero_eqtopa {R : Type u} [CommSemiring R]
    (F : fAlg R) : F.filtration 0 = ⊤ :=
  F.exhaustive_zero

/-- Powers of the augmentation ideal. -/
noncomputable def powersAugmentationIdeal
    (R : Type u) (G : Type v) [CommRing R] [Group G] (n : ℕ) :
    Ideal (MonoidAlgebra R G) :=
  (augmentationIdeal R G) ^ n

/-- View an augmentation-ideal power as an `R`-submodule of the group algebra. -/
noncomputable abbrev augmentationPowerSubmodule (R : Type u) (G : Type v)
    [CommRing R] [Group G] (n : ℕ) : Submodule R (MonoidAlgebra R G) :=
  Submodule.restrictScalars R (powersAugmentationIdeal R G n)

/-- The concrete quotient `I^n/I^(n+1)` as an `R`-module quotient. -/
noncomputable abbrev augmentationLayerQuotient (R : Type u) (G : Type v)
    [CommRing R] [Group G] (n : ℕ) : Type (max u v) :=
  (augmentationPowerSubmodule R G n) ⧸
    Submodule.comap (Submodule.subtype (augmentationPowerSubmodule R G n))
      (augmentationPowerSubmodule R G (n + 1))

/-- Augmentation layers, with an explicit identification with `I^n/I^(n+1)`. -/
structure augmentationLayers (R : Type u) (G : Type v) [CommRing R] [Group G] where
  degree : ℕ
  carrier : Type (max u v)
  [addCarrier : AddCommGroup carrier]
  [moduleCarrier : Module R carrier]
  linearEquivQuotient : carrier ≃ₗ[R] augmentationLayerQuotient R G degree

attribute [instance] augmentationLayers.addCarrier augmentationLayers.moduleCarrier

/-- Linear part of a relator in degree one, with a nonzero witness when the
relator contributes a genuine degree-one relation. -/
structure lPRelato (R : Type u) (α : Type v) [Semiring R] where
  relator : FreeGroup α
  linear : α → R
  nonzeroGenerator : α
  nonzero : linear nonzeroGenerator ≠ 0
  finiteSupport : Set.Finite {a : α | linear a ≠ 0}
  relator_nontrivial : relator ≠ 1

/-- The displayed nonzero generator really has nonzero linear coefficient. -/
theorem lPRelato.nonzero_at_generator {R : Type u} {α : Type v} [Semiring R]
    (L : lPRelato R α) : L.linear L.nonzeroGenerator ≠ 0 := L.nonzero

/-- The support of a linear relator is finite. -/
theorem lPRelato.support_finite {R : Type u} {α : Type v} [Semiring R]
    (L : lPRelato R α) : Set.Finite {a : α | L.linear a ≠ 0} :=
  L.finiteSupport

/-- The underlying relator is nontrivial. -/
theorem lPRelato.relator_ne_one {R : Type u} {α : Type v} [Semiring R]
    (L : lPRelato R α) : L.relator ≠ 1 := L.relator_nontrivial

/-- Degree-one GS layer data. -/
structure dGLayer where
  p : ℕ
  prime : Nat.Prime p
  generators : Type u
  rank : Cardinal.{u}
  linearRelations : Type v
  [relationAdd : AddCommGroup linearRelations]
  [rModule : Module (ZMod p) linearRelations]
  relationVector : generators → linearRelations
  span_relations : Submodule.span (ZMod p) (Set.range relationVector) = ⊤
  rank_eq : rank = Cardinal.mk generators

attribute [instance] dGLayer.relationAdd dGLayer.rModule

/-- The stored primality witness supplies the usual `Fact` instance for `ZMod L.p`. -/
instance dGLayer.fact_prime (L : dGLayer.{u, v}) : Fact L.p.Prime :=
  ⟨L.prime⟩

/-- The stored rank is the cardinality of the generator type. -/
theorem dGLayer.rank_spec (L : dGLayer.{u, v}) :
    L.rank = Cardinal.mk L.generators := L.rank_eq

/-- The relation vectors span the relation module. -/
theorem dGLayer.span_relationVector (L : dGLayer.{u, v}) :
    Submodule.span (ZMod L.p) (Set.range L.relationVector) = ⊤ :=
  L.span_relations

/-- The prime attached to a degree-one GS layer. -/
theorem dGLayer.prime_p (L : dGLayer.{u, v}) : Nat.Prime L.p :=
  L.prime

/-- The predicate/marker for degrees at least two. -/
def dGTwo (n : ℕ) : Prop := 2 ≤ n

@[simp] theorem degrees_two_zero : ¬ dGTwo 0 := by
  unfold dGTwo
  omega

@[simp] theorem degrees_two_one : ¬ dGTwo 1 := by
  unfold dGTwo
  omega

/-- Degrees at least two are upward closed. -/
theorem dGTwo.mono {m n : ℕ} (hm : dGTwo m) (h : m ≤ n) :
    dGTwo n := by
  unfold dGTwo at *
  omega

/-- `n+2` is always a degree at least two. -/
theorem degrees_two_add (n : ℕ) : dGTwo (n + 2) := by
  unfold dGTwo
  omega

/-- The augmentation filtration by powers of the augmentation ideal. -/
noncomputable def augmentationFiltration (R : Type u) (G : Type v) [CommRing R] [Group G] :
    ℕ → Ideal (MonoidAlgebra R G) :=
  powersAugmentationIdeal R G

/-- Associated graded group algebra, packaged by layers. -/
structure aGAlg (R : Type u) (G : Type v) [CommRing R] [Group G] where
  layer : ℕ → Type (max u v)
  [addLayer : ∀ n, AddCommGroup (layer n)]
  [moduleLayer : ∀ n, Module R (layer n)]
  equivAugmentationLayer : ∀ n, layer n ≃ₗ[R] augmentationLayerQuotient R G n
  mul : ∀ m n, layer m → layer n → layer (m + n)
  one : layer 0
  mul_add_left : ∀ m n (x y : layer m) (z : layer n),
    mul m n (x + y) z = mul m n x z + mul m n y z
  mul_add_right : ∀ m n (x : layer m) (y z : layer n),
    mul m n x (y + z) = mul m n x y + mul m n x z
  mul_zero_left : ∀ m n (z : layer n), mul m n (0 : layer m) z = 0
  mul_zero_right : ∀ m n (x : layer m), mul m n x (0 : layer n) = 0
  one_mul : ∀ n (x : layer n), HEq (mul 0 n one x) x
  mul_one : ∀ n (x : layer n), HEq (mul n 0 x one) x
  mul_assoc : ∀ l m n (x : layer l) (y : layer m) (z : layer n),
    HEq (mul (l + m) n (mul l m x y) z)
         (mul l (m + n) x (mul m n y z))

attribute [instance] aGAlg.addLayer
attribute [instance] aGAlg.moduleLayer

@[simp] theorem aGAlg.mul_zero_leftapply {R : Type u} {G : Type v}
    [CommRing R] [Group G] (A : aGAlg R G)
    (m n : ℕ) (z : A.layer n) : A.mul m n (0 : A.layer m) z = 0 :=
  A.mul_zero_left m n z

@[simp] theorem aGAlg.mul_zero_rightapply {R : Type u} {G : Type v}
    [CommRing R] [Group G] (A : aGAlg R G)
    (m n : ℕ) (x : A.layer m) : A.mul m n x (0 : A.layer n) = 0 :=
  A.mul_zero_right m n x

/-- Left additivity of multiplication in the associated graded group algebra. -/
theorem aGAlg.mul_add_leftapply {R : Type u} {G : Type v}
    [CommRing R] [Group G] (A : aGAlg R G)
    (m n : ℕ) (x y : A.layer m) (z : A.layer n) :
    A.mul m n (x + y) z = A.mul m n x z + A.mul m n y z :=
  A.mul_add_left m n x y z

/-- Right additivity of multiplication in the associated graded group algebra. -/
theorem aGAlg.mul_add_rightapply {R : Type u} {G : Type v}
    [CommRing R] [Group G] (A : aGAlg R G)
    (m n : ℕ) (x : A.layer m) (y z : A.layer n) :
    A.mul m n x (y + z) = A.mul m n x y + A.mul m n x z :=
  A.mul_add_right m n x y z

/-- Associativity accessor for the associated graded group algebra. -/
theorem aGAlg.mul_assoc_heq {R : Type u} {G : Type v}
    [CommRing R] [Group G] (A : aGAlg R G)
    (l m n : ℕ) (x : A.layer l) (y : A.layer m) (z : A.layer n) :
    HEq (A.mul (l + m) n (A.mul l m x y) z)
         (A.mul l (m + n) x (A.mul m n y z)) :=
  A.mul_assoc l m n x y z

/-- Left unit accessor for the associated graded group algebra. -/
theorem aGAlg.one_mul_heq {R : Type u} {G : Type v}
    [CommRing R] [Group G] (A : aGAlg R G)
    (n : ℕ) (x : A.layer n) : HEq (A.mul 0 n A.one x) x :=
  A.one_mul n x

/-- Right unit accessor for the associated graded group algebra. -/
theorem aGAlg.mul_one_heq {R : Type u} {G : Type v}
    [CommRing R] [Group G] (A : aGAlg R G)
    (n : ℕ) (x : A.layer n) : HEq (A.mul n 0 x A.one) x :=
  A.mul_one n x

/-- The displayed degree-zero unit of an associated graded group algebra. -/
def aGAlg.unit {R : Type u} {G : Type v}
    [CommRing R] [Group G] (A : aGAlg R G) : A.layer 0 :=
  A.one

/-- Augmentation degree of an algebra element, if known. -/
def augmentationAlgebraElement (R : Type u) (G : Type v) [CommRing R] [Group G]
    (x : MonoidAlgebra R G) : Type :=
  {n : ℕ // x ∈ powersAugmentationIdeal R G n ∧
    x ∉ powersAugmentationIdeal R G (n + 1)}

/-- The canonical Fox coefficients of a relator. -/
noncomputable def initialFoxCoefficients (R : Type u) (α : Type v) [Ring R]
    (relator : FreeGroup α) : α → MonoidAlgebra R (FreeGroup α) :=
  fun a => Submission.Theorems.foxD (R := R) a relator

/-- Initial Fox form of a relator, retaining the source relator and the claim
that its canonical Fox coefficients are homogeneous in the chosen initial degree. -/
structure iFForm (R : Type u) (α : Type v) [Ring R] where
  relator : FreeGroup α
  degree : ℕ
  coefficientDegree : α → ℕ
  nonzero : ∃ a, initialFoxCoefficients R α relator a ≠ 0
  homogeneous : ∀ a, initialFoxCoefficients R α relator a ≠ 0 →
    coefficientDegree a = degree

/-- The coefficient vector of an initial Fox form is the canonical Fox derivative
of the stored relator. -/
noncomputable def iFForm.coeff {R : Type u} {α : Type v} [Ring R]
    (F : iFForm R α) : α → MonoidAlgebra R (FreeGroup α) :=
  initialFoxCoefficients R α F.relator

/-- A nonzero coefficient in an initial Fox form has the displayed degree. -/
theorem iFForm.degree_coeff_nezero {R : Type u} {α : Type v} [Ring R]
    (F : iFForm R α) {a : α} (ha : F.coeff a ≠ 0) :
    F.coefficientDegree a = F.degree :=
  F.homogeneous a (by simpa [iFForm.coeff] using ha)

/-- There is at least one nonzero coefficient in an initial Fox form. -/
theorem iFForm.exists_nonzero_coeff {R : Type u} {α : Type v} [Ring R]
    (F : iFForm R α) : ∃ a, F.coeff a ≠ 0 := by
  rcases F.nonzero with ⟨a, ha⟩
  exact ⟨a, by simpa [iFForm.coeff] using ha⟩

/-- Initial Fox forms for active relators. -/
def foxFormsRelators (R : Type u) (α : Type v) [Ring R]
    (A : Set (FreeGroup α)) :=
  A → iFForm R α

/-- Initial Fox matrix, indexed by relators and generators. -/
abbrev initialFoxMatrix (R : Type u) (α : Type v) [Semiring R] :=
  FreeGroup α → α → MonoidAlgebra R (FreeGroup α)

/-- Multiplication in an associated graded object, degree-aware and bilinear in
each homogeneous degree. -/
structure aGMultip (R : Type u) [Semiring R]
    (A : ℕ → Type v) where
  [addA : ∀ n, AddCommMonoid (A n)]
  [modA : ∀ n, Module R (A n)]
  mul : ∀ m n, A m → A n → A (m+n)
  mul_add_left : ∀ m n (x y : A m) (z : A n),
    mul m n (x + y) z = mul m n x z + mul m n y z
  mul_add_right : ∀ m n (x : A m) (y z : A n),
    mul m n x (y + z) = mul m n x y + mul m n x z
  mul_smul_left : ∀ m n (r : R) (x : A m) (y : A n),
    mul m n (r • x) y = r • mul m n x y
  mul_smul_right : ∀ m n (r : R) (x : A m) (y : A n),
    mul m n x (r • y) = r • mul m n x y
  mul_zero_left : ∀ m n (y : A n), mul m n (0 : A m) y = 0
  mul_zero_right : ∀ m n (x : A m), mul m n x (0 : A n) = 0
  /-- A homogeneous unit in degree zero. -/
  one : A 0
  /-- Left unit law (definitionally `0+n = n`, but kept as heterogeneous for uniformity). -/
  one_mul : ∀ n (x : A n), HEq (mul 0 n one x) x
  /-- Right unit law across the definitional/cast boundary `n+0 = n`. -/
  mul_one : ∀ n (x : A n), HEq (mul n 0 x one) x
  /-- Associativity across the two parenthesizations of degree addition. -/
  mul_assoc : ∀ l m n (x : A l) (y : A m) (z : A n),
    HEq (mul (l + m) n (mul l m x y) z)
         (mul l (m + n) x (mul m n y z))

/-- Associativity accessor for graded multiplication (heterogeneous because degrees reassociate). -/
theorem aGMultip.mul_assoc_heq {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (l m n : ℕ) (x : A l) (y : A m) (z : A n) :
    HEq (M.mul (l + m) n (M.mul l m x y) z)
         (M.mul l (m + n) x (M.mul m n y z)) :=
  M.mul_assoc l m n x y z

/-- Left unit accessor for graded multiplication. -/
theorem aGMultip.one_mul_heq {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (n : ℕ) (x : A n) : HEq (M.mul 0 n M.one x) x :=
  M.one_mul n x

/-- Right unit accessor for graded multiplication. -/
theorem aGMultip.mul_one_heq {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (n : ℕ) (x : A n) : HEq (M.mul n 0 x M.one) x :=
  M.mul_one n x

@[simp] theorem aGMultip.mul_zero_leftapply {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (m n : ℕ) (y : A n) :
    (letI := M.addA m; letI := M.addA (m + n); M.mul m n (0 : A m) y = 0) := by
  exact M.mul_zero_left m n y

@[simp] theorem aGMultip.mul_zero_rightapply {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (m n : ℕ) (x : A m) :
    (letI := M.addA n; letI := M.addA (m + n); M.mul m n x (0 : A n) = 0) := by
  exact M.mul_zero_right m n x

/-- Scalar compatibility on the left for graded multiplication. -/
theorem aGMultip.mul_smul_leftapply {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (m n : ℕ) (r : R) (x : A m) (y : A n) :
    (letI := M.modA m; letI := M.modA (m + n);
      M.mul m n (r • x) y = r • M.mul m n x y) := by
  exact M.mul_smul_left m n r x y

/-- Scalar compatibility on the right for graded multiplication. -/
theorem aGMultip.mul_smul_rightapply {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (m n : ℕ) (r : R) (x : A m) (y : A n) :
    (letI := M.modA n; letI := M.modA (m + n);
      M.mul m n x (r • y) = r • M.mul m n x y) := by
  exact M.mul_smul_right m n r x y

/-- Left additivity for graded multiplication. -/
theorem aGMultip.mul_add_leftapply {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (m n : ℕ) (x y : A m) (z : A n) :
    (letI := M.addA m; letI := M.addA (m + n);
      M.mul m n (x + y) z = M.mul m n x z + M.mul m n y z) := by
  exact M.mul_add_left m n x y z

/-- Right additivity for graded multiplication. -/
theorem aGMultip.mul_add_rightapply {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (m n : ℕ) (x : A m) (y z : A n) :
    (letI := M.addA n; letI := M.addA (m + n);
      M.mul m n x (y + z) = M.mul m n x y + M.mul m n x z) := by
  exact M.mul_add_right m n x y z

/-- Multiplication maps by generators, with degree-one shifts. -/
structure gMMaps (R : Type u) [Semiring R]
    (A : ℕ → Type v) (ι : Type w) where
  [addA : ∀ n, AddCommMonoid (A n)]
  [modA : ∀ n, Module R (A n)]
  multiplication : aGMultip R A
  generator : ι → A 1
  generator_nonzero : ∀ i, generator i ≠ 0
  map : ι → ∀ n, A n →ₗ[R] A (n+1)
  map_eq_mul : ∀ i n x, map i n x = multiplication.mul n 1 x (generator i)

/-- Generator multiplication maps are given by right multiplication by the generator. -/
theorem gMMaps.map_apply_eqmul {R : Type u} [Semiring R]
    {A : ℕ → Type v} {ι : Type w} (M : gMMaps R A ι)
    (i : ι) (n : ℕ) (x : A n) :
    M.map i n x = M.multiplication.mul n 1 x (M.generator i) :=
  M.map_eq_mul i n x

/-- Recorded generators are nonzero. -/
theorem gMMaps.generator_ne_zero {R : Type u} [Semiring R]
    {A : ℕ → Type v} {ι : Type w} (M : gMMaps R A ι) (i : ι) :
    (letI := M.addA 1; M.generator i ≠ 0) := by
  exact M.generator_nonzero i

/-- A homogeneous syzygy among generator multiplication maps: a finite linear
combination of degree-`n` inputs whose multiplied images in degree `n+1` sum to
zero. -/
structure sAMultip (R : Type u) [Semiring R]
    (A : ℕ → Type v) (ι : Type w) [Fintype ι] [DecidableEq ι] where
  [addA : ∀ n, AddCommMonoid (A n)]
  [modA : ∀ n, Module R (A n)]
  maps : gMMaps R A ι
  degree : ℕ
  coeff : ι → A degree
  nontrivial : ∃ i, coeff i ≠ 0
  support : Finset ι
  support_spec : ∀ i, i ∈ support ↔ coeff i ≠ 0
  relation : Finset.sum Finset.univ (fun i : ι => maps.map i degree (coeff i)) = 0
  relation_on_support : Finset.sum support (fun i : ι => maps.map i degree (coeff i)) = 0
  minimal_support : ∀ j, j ∈ support →
    Finset.sum (support.erase j) (fun i : ι => maps.map i degree (coeff i)) ≠ 0

/-- Support membership for a homogeneous syzygy is exactly nonzero coefficient. -/
theorem sAMultip.mem_support_iff {R : Type u}
    [Semiring R] {A : ℕ → Type v} {ι : Type w} [Fintype ι] [DecidableEq ι]
    (S : sAMultip R A ι) (i : ι) :
    (letI := S.addA S.degree; i ∈ S.support ↔ S.coeff i ≠ 0) := by
  exact S.support_spec i

/-- A homogeneous syzygy has a nonzero coefficient. -/
theorem sAMultip.exists_nonzero {R : Type u}
    [Semiring R] {A : ℕ → Type v} {ι : Type w} [Fintype ι] [DecidableEq ι]
    (S : sAMultip R A ι) :
    (letI := S.addA S.degree; ∃ i, S.coeff i ≠ 0) := by
  exact S.nontrivial

/-- Boundary map for a relation module. -/
structure rMBounda (R : Type u) [Semiring R] where
  M : Type v
  N : Type w
  [addM : AddCommMonoid M]
  [modM : Module R M]
  [addN : AddCommMonoid N]
  [modN : Module R N]
  map : M →ₗ[R] N
  kernel : Submodule R M := LinearMap.ker map
  range : Submodule R N := LinearMap.range map
  kills : ∀ x : kernel, map x.1 = 0
  kernel_eq : kernel = LinearMap.ker map
  range_eq : range = LinearMap.range map

attribute [instance] rMBounda.addM rMBounda.modM
attribute [instance] rMBounda.addN rMBounda.modN

/-- A syzygy module packaged as the kernel of an explicit linear map. -/
structure sModule (R : Type u) [Semiring R] where
  M : Type v
  N : Type w
  [addM : AddCommMonoid M]
  [modM : Module R M]
  [addN : AddCommMonoid N]
  [modN : Module R N]
  boundary : M →ₗ[R] N
  equations : Submodule R M := LinearMap.ker boundary
  inclusion : equations →ₗ[R] M := Submodule.subtype equations
  boundary_zero : ∀ x : equations, boundary x.1 = 0
  equations_eq_kernel : equations = LinearMap.ker boundary
  inclusion_eq_subtype : inclusion = Submodule.subtype equations

attribute [instance] sModule.addM sModule.modM
attribute [instance] sModule.addN sModule.modN


/-- Build a boundary-map package from a linear map. -/
def rMBounda.ofMap (R : Type u) [Semiring R]
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) : rMBounda R where
  M := M
  N := N
  map := f
  kernel := LinearMap.ker f
  range := LinearMap.range f
  kills := by intro x; exact x.2
  kernel_eq := rfl
  range_eq := rfl

@[simp] theorem rMBounda.ofMap_map (R : Type u) [Semiring R]
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (rMBounda.ofMap R M N f).map = f := rfl

@[simp] theorem rMBounda.ofMap_kernel (R : Type u) [Semiring R]
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (rMBounda.ofMap R M N f).kernel = LinearMap.ker f := rfl

/-- Elements of a boundary-map kernel are killed by the map. -/
theorem rMBounda.map_eqzero_memkernel {R : Type u} [Semiring R]
    (B : rMBounda R) (x : B.kernel) : B.map x.1 = 0 :=
  B.kills x

/-- The recorded kernel of a boundary-map package is the actual kernel. -/
theorem rMBounda.kernel_eq_kernel {R : Type u} [Semiring R]
    (B : rMBounda R) : B.kernel = LinearMap.ker B.map :=
  B.kernel_eq

/-- The recorded range of a boundary-map package is the actual range. -/
theorem rMBounda.range_eq_range {R : Type u} [Semiring R]
    (B : rMBounda R) : B.range = LinearMap.range B.map :=
  B.range_eq

/-- Build a syzygy module as the kernel of a linear map. -/
def sModule.ofBoundary (R : Type u) [Semiring R]
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) : sModule R where
  M := M
  N := N
  boundary := f
  equations := LinearMap.ker f
  inclusion := Submodule.subtype (LinearMap.ker f)
  boundary_zero := by intro x; exact x.2
  equations_eq_kernel := rfl
  inclusion_eq_subtype := rfl

@[simp] theorem sModule.ofBoundary_boundary (R : Type u) [Semiring R]
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (sModule.ofBoundary R M N f).boundary = f := rfl

@[simp] theorem sModule.ofBoundary_equations (R : Type u) [Semiring R]
    (M : Type v) (N : Type w) [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (sModule.ofBoundary R M N f).equations = LinearMap.ker f := rfl

/-- The displayed inclusion of a syzygy module is the canonical subtype map. -/
theorem sModule.inclusion_eq {R : Type u} [Semiring R]
    (S : sModule R) : S.inclusion = Submodule.subtype S.equations :=
  S.inclusion_eq_subtype

/-- A syzygy equation element is killed by the boundary. -/
theorem sModule.boundary_eq_zero {R : Type u} [Semiring R]
    (S : sModule R) (x : S.equations) : S.boundary x.1 = 0 :=
  S.boundary_zero x

/-- Membership in the syzygy equations is exactly vanishing under the boundary. -/
theorem sModule.mem_equations_iff {R : Type u} [Semiring R]
    (S : sModule R) (x : S.M) : x ∈ S.equations ↔ S.boundary x = 0 := by
  rw [S.equations_eq_kernel]
  rfl

/-- Linearization of a relator. -/
abbrev linearizationRelator (R : Type u) (α : Type v) [Semiring R] := lPRelato R α

/-- Dimension subgroup defined by augmentation-power membership. -/
def dSubgro (R : Type u) (G : Type v) [CommRing R] [Group G] (n : ℕ) : Set G :=
  {g | (MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈ powersAugmentationIdeal R G n}

/-- A bundled subgroup model for a dimension subgroup.  The raw predicate
`dSubgro` is convenient for unfolding augmentation-power membership,
but the mathematical object is a (normal) subgroup; this package records the
subgroup operations and ties them exactly to the predicate. -/
structure dSModel (R : Type u) (G : Type v) [CommRing R] [Group G]
    (n : ℕ) where
  subgroup : Subgroup G
  mem_iff : ∀ g : G, g ∈ subgroup ↔ g ∈ dSubgro R G n
  normal' : subgroup.Normal

attribute [instance] dSModel.normal'

/-- Membership in a bundled dimension subgroup is exactly augmentation-power membership. -/
theorem dSModel.mem_iff' {R : Type u} {G : Type v}
    [CommRing R] [Group G] {n : ℕ} (D : dSModel R G n) (g : G) :
    g ∈ D.subgroup ↔ g ∈ dSubgro R G n :=
  D.mem_iff g

/-- The carrier set of a bundled dimension subgroup is the raw dimension-subgroup predicate. -/
theorem dSModel.carrier_eq {R : Type u} {G : Type v}
    [CommRing R] [Group G] {n : ℕ} (D : dSModel R G n) :
    (D.subgroup : Set G) = dSubgro R G n := by
  ext g
  exact D.mem_iff g

/-- A bundled dimension subgroup is normal. -/
theorem dSModel.normal {R : Type u} {G : Type v}
    [CommRing R] [Group G] {n : ℕ} (D : dSModel R G n) :
    D.subgroup.Normal :=
  D.normal'

/-- Zassenhaus/Jennings quotients by filtration terms.  The quotient models are
explicitly identified with the successive filtration layers, rather than being
bare degree-indexed types. -/
structure zJQuotie (G : Type u) [Group G] where
  filtration : DFilt G
  quotient : ℕ → Type u
  equivLayer : ∀ n, quotient n ≃ filtrationLayer filtration n
  zeroClass : ∀ n, quotient n
  zero_matches_one : ∀ n, equivLayer n (zeroClass n) = 1

/-- The distinguished zero class corresponds to the identity layer element. -/
@[simp] theorem zJQuotie.zeroClass_equiv {G : Type u} [Group G]
    (Z : zJQuotie G) (n : ℕ) :
    Z.equivLayer n (Z.zeroClass n) = 1 := Z.zero_matches_one n

/-- The zero class is the inverse image of the identity under the layer equivalence. -/
theorem zJQuotie.zero_classeq_symmone {G : Type u} [Group G]
    (Z : zJQuotie G) (n : ℕ) :
    Z.zeroClass n = (Z.equivLayer n).symm 1 := by
  apply (Z.equivLayer n).injective
  simp [Z.zeroClass_equiv]

/-- Truncated Jennings comparison data up to a cutoff, with mutually inverse
comparison maps in every retained degree. -/
structure tJCompar where
  cutoff : ℕ
  source : ℕ → Type u
  target : ℕ → Type v
  toTarget : ∀ n, n ≤ cutoff → source n → target n
  toSource : ∀ n, n ≤ cutoff → target n → source n
  left_inv : ∀ n (h : n ≤ cutoff) (x : source n), toSource n h (toTarget n h x) = x
  right_inv : ∀ n (h : n ≤ cutoff) (y : target n), toTarget n h (toSource n h y) = y

/-- The comparison data gives an equivalence in each retained degree. -/
def tJCompar.equiv (C : tJCompar.{u, v})
    (n : ℕ) (h : n ≤ C.cutoff) : C.source n ≃ C.target n where
  toFun := C.toTarget n h
  invFun := C.toSource n h
  left_inv := C.left_inv n h
  right_inv := C.right_inv n h

@[simp] theorem tJCompar.equiv_apply
    (C : tJCompar.{u, v}) (n : ℕ) (h : n ≤ C.cutoff) (x : C.source n) :
    C.equiv n h x = C.toTarget n h x := rfl

@[simp] theorem tJCompar.equiv_symm_apply
    (C : tJCompar.{u, v}) (n : ℕ) (h : n ≤ C.cutoff) (y : C.target n) :
    (C.equiv n h).symm y = C.toSource n h y := rfl

@[simp] theorem tJCompar.source_target
    (C : tJCompar.{u, v}) (n : ℕ) (h : n ≤ C.cutoff) (x : C.source n) :
    C.toSource n h (C.toTarget n h x) = x := C.left_inv n h x

@[simp] theorem tJCompar.target_source
    (C : tJCompar.{u, v}) (n : ℕ) (h : n ≤ C.cutoff) (y : C.target n) :
    C.toTarget n h (C.toSource n h y) = y := C.right_inv n h y

/-- Threshold degree for exactness statements. -/
abbrev exactnessThresholdDegree := ℕ

/-- Nilpotence index of the augmentation ideal, if it exists. -/
def nIIdeal (R : Type u) (G : Type v) [CommRing R] [Group G] : Type :=
  {n : ℕ // powersAugmentationIdeal R G n = ⊥ ∧
    ∀ m, m < n → powersAugmentationIdeal R G m ≠ ⊥}


/-- Membership in a dimension subgroup, unfolded. -/
@[simp] theorem dSubgro.mem_iff {R : Type u} {G : Type v}
    [CommRing R] [Group G] (n : ℕ) (g : G) :
    g ∈ dSubgro R G n ↔
      (MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈ powersAugmentationIdeal R G n :=
  Iff.rfl

/-- A nilpotence index really kills the corresponding augmentation power. -/
theorem nIIdeal.power_eq_bot {R : Type u} {G : Type v}
    [CommRing R] [Group G] (N : nIIdeal R G) :
    powersAugmentationIdeal R G N.1 = ⊥ :=
  N.2.1

/-- Smaller powers before a nilpotence index are nonzero. -/
theorem nIIdeal.prev_ne_bot {R : Type u} {G : Type v}
    [CommRing R] [Group G] (N : nIIdeal R G)
    {m : ℕ} (hm : m < N.1) : powersAugmentationIdeal R G m ≠ ⊥ :=
  N.2.2 m hm

/-- A filtered module, using actual submodules as filtration terms.  This makes
quotients and induced graded maps available without rebuilding linear closure
from bare sets. -/
structure fModule (R : Type u) [Semiring R] where
  M : Type v
  [addM : AddCommGroup M]
  [modM : Module R M]
  filtration : ℕ → Submodule R M
  exhaustive_zero : filtration 0 = ⊤
  antitone : ∀ {m n}, m ≤ n → filtration n ≤ filtration m

attribute [instance] fModule.addM fModule.modM

/-- Every element of a filtered module lies in filtration degree zero. -/
theorem fModule.mem_zero {R : Type u} [Semiring R]
    (F : fModule R) (x : F.M) : x ∈ F.filtration 0 := by
  rw [F.exhaustive_zero]
  trivial

/-- Antitonicity of filtered-module terms, pointwise. -/
theorem fModule.mem_of_le {R : Type u} [Semiring R]
    (F : fModule R) {m n : ℕ} (h : m ≤ n) {x : F.M}
    (hx : x ∈ F.filtration n) : x ∈ F.filtration m :=
  F.antitone h hx

/-- The zeroth filtration term of a filtered module is the whole module. -/
@[simp] theorem fModule.filt_zero_eqtopa {R : Type u} [Semiring R]
    (F : fModule R) : F.filtration 0 = ⊤ :=
  F.exhaustive_zero

/-- Named antitonicity inclusion for filtered modules. -/
theorem fModule.subset_of_le {R : Type u} [Semiring R]
    (F : fModule R) {m n : ℕ} (h : m ≤ n) :
    F.filtration n ≤ F.filtration m :=
  F.antitone h

/-- The `(n)/(n+1)` quotient layer of a filtered module. -/
abbrev filteredModuleLayer (R : Type u) [Ring R] (M : fModule R) (n : ℕ) : Type v :=
  (M.filtration n) ⧸ Submodule.comap (Submodule.subtype (M.filtration n))
    (M.filtration (n + 1))

/-- Associated graded module of a filtered module, represented by degree-indexed
pieces together with quotient projections from filtration terms. -/
structure aGModule (R : Type u) [Semiring R] where
  source : fModule.{u, v} R
  piece : ℕ → Type v
  [addPiece : ∀ n, AddCommGroup (piece n)]
  [modulePiece : ∀ n, Module R (piece n)]
  projection : ∀ n, source.filtration n →ₗ[R] piece n
  projection_surjective : ∀ n, Function.Surjective (projection n)
  kernel_next : ∀ n, LinearMap.ker (projection n) =
    Submodule.comap (Submodule.subtype (source.filtration n)) (source.filtration (n + 1))

attribute [instance] aGModule.addPiece aGModule.modulePiece

/-- Projections from an associated graded module are surjective in each degree. -/
theorem aGModule.projection_surj {R : Type u} [Semiring R]
    (A : aGModule R) (n : ℕ) : Function.Surjective (A.projection n) :=
  A.projection_surjective n

/-- The kernel of the projection is the next filtration term. -/
theorem aGModule.kernel_projection {R : Type u} [Semiring R]
    (A : aGModule R) (n : ℕ) :
    LinearMap.ker (A.projection n) =
      Submodule.comap (Submodule.subtype (A.source.filtration n)) (A.source.filtration (n + 1)) :=
  A.kernel_next n

/-- A graded exact sequence of modules, degree by degree.  The maps are linear,
so this can be used directly for Hilbert-dimension arguments. -/
structure gESequen (R : Type u) [Semiring R]
    (A B C : ℕ → Type v) where
  [addA : ∀ n, AddCommMonoid (A n)]
  [addB : ∀ n, AddCommMonoid (B n)]
  [addC : ∀ n, AddCommMonoid (C n)]
  [modA : ∀ n, Module R (A n)]
  [modB : ∀ n, Module R (B n)]
  [modC : ∀ n, Module R (C n)]
  f : ∀ n, A n →ₗ[R] B n
  g : ∀ n, B n →ₗ[R] C n
  complex : ∀ n (a : A n), g n (f n a) = 0
  exact : ∀ n (b : B n), g n b = 0 ↔ ∃ a : A n, f n a = b

/-- The composite in a graded exact sequence is zero in each degree. -/
theorem gESequen.complex_apply {R : Type u} [Semiring R]
    {A B C : ℕ → Type v} (E : gESequen R A B C)
    (n : ℕ) (a : A n) :
    (letI := E.addA n; letI := E.addB n; letI := E.addC n
     letI := E.modA n; letI := E.modB n; letI := E.modC n
     E.g n (E.f n a) = 0) := by
  exact E.complex n a

/-- Exactness criterion in a graded exact sequence, as a named iff. -/
theorem gESequen.exact_iff {R : Type u} [Semiring R]
    {A B C : ℕ → Type v} (E : gESequen R A B C)
    (n : ℕ) (b : B n) :
    (letI := E.addA n; letI := E.addB n; letI := E.addC n
     letI := E.modA n; letI := E.modB n; letI := E.modC n
     E.g n b = 0 ↔ ∃ a : A n, E.f n a = b) := by
  exact E.exact n b

/-- Exactness as equality of range and kernel in each degree. -/
theorem gESequen.range_eq_ker {R : Type u} [Semiring R]
    {A B C : ℕ → Type v} (E : gESequen R A B C) (n : ℕ) :
    letI := E.addA n; letI := E.addB n; letI := E.addC n
    letI := E.modA n; letI := E.modB n; letI := E.modC n
    LinearMap.range (E.f n) = LinearMap.ker (E.g n) := by
  letI := E.addA n; letI := E.addB n; letI := E.addC n
  letI := E.modA n; letI := E.modB n; letI := E.modC n
  ext b
  constructor
  · intro hb
    rcases hb with ⟨a, rfl⟩
    exact E.complex n a
  · intro hb
    exact (E.exact n b).1 hb

/-- Degree shift of a graded module. -/
def shiftGradedModule (A : ℕ → Type u) (q : ℕ) : ℕ → Type u :=
  fun n => A (n + q)

/-- Graded generator module: a degree-one family with explicit spanning and
minimality predicates for the first graded piece. -/
structure gGModule (ι : Type u) where
  piece : ℕ → Type v
  [addPiece : ∀ n, AddCommMonoid (piece n)]
  generator : ι → piece 1
  spans_degree_one : Function.Surjective generator
  minimal_degree_one : ∀ i j, generator i = generator j → i = j
  nonzero_generators : ∀ i, generator i ≠ 0

attribute [instance] gGModule.addPiece

/-- Degree-one generators are surjective onto the first piece. -/
theorem gGModule.generator_surjective {ι : Type u}
    (Gm : gGModule ι) : Function.Surjective Gm.generator :=
  Gm.spans_degree_one

/-- Minimality gives injectivity of the generator map. -/
theorem gGModule.generator_injective {ι : Type u}
    (Gm : gGModule ι) : Function.Injective Gm.generator :=
  fun _ _ h => Gm.minimal_degree_one _ _ h

/-- Recorded degree-one generators are nonzero. -/
theorem gGModule.generator_ne_zero {ι : Type u}
    (Gm : gGModule ι) (i : ι) :
    (letI := Gm.addPiece 1; Gm.generator i ≠ 0) := by
  exact Gm.nonzero_generators i

/-- Degree-one generators form a bijective parametrization of the first piece. -/
theorem gGModule.generator_bijective {ι : Type u}
    (Gm : gGModule ι) : Function.Bijective Gm.generator :=
  ⟨Gm.generator_injective, Gm.generator_surjective⟩

/-- Multiplication by one generator on graded pieces, as linear maps. -/
structure gMMap (R : Type u) [Semiring R] (A : ℕ → Type v) where
  gen : Type w
  [addA : ∀ n, AddCommMonoid (A n)]
  [modA : ∀ n, Module R (A n)]
  multiplication : aGMultip R A
  generator : gen → A 1
  generator_nonzero : ∀ i, generator i ≠ 0
  map : gen → ∀ n, A n →ₗ[R] A (n+1)
  map_eq_mul : ∀ i n x, map i n x = multiplication.mul n 1 x (generator i)

/-- The recorded generator is nonzero (projection lemma with local instances). -/
theorem gMMap.generator_ne_zero {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : gMMap R A) (i : M.gen) :
    (letI := M.addA 1; M.generator i ≠ 0) := by
  exact M.generator_nonzero i

/-- Multiplication maps are exactly right multiplication by the chosen generator. -/
theorem gMMap.map_apply_eqmul {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : gMMap R A) (i : M.gen)
    (n : ℕ) (x : A n) :
    (letI := M.addA n; letI := M.addA 1; letI := M.addA (n + 1)
     letI := M.modA n; letI := M.modA (n + 1)
     M.map i n x = M.multiplication.mul n 1 x (M.generator i)) := by
  exact M.map_eq_mul i n x

/-- Weight of the actual group commutator under a weight function.  Lower-bound
properties such as `w [x,y] ≥ w x + w y` should be supplied separately. -/
def commutatorWeight {G : Type u} [Group G] (w : G → ℕ) (x y : G) : ℕ :=
  w (x * y * x⁻¹ * y⁻¹)


@[simp] theorem shift_graded_module (A : ℕ → Type u) (q n : ℕ) :
    shiftGradedModule A q n = A (n + q) := rfl

@[simp] theorem commutator_weight {G : Type u} [Group G] (w : G → ℕ) (x y : G) :
    commutatorWeight w x y = w (x * y * x⁻¹ * y⁻¹) := rfl

/-- A separate lower-bound predicate for commutator weights. -/
def commutatorLowerBound {G : Type u} [Group G] (w : G → ℕ) : Prop :=
  ∀ x y : G, w x + w y ≤ commutatorWeight w x y


end Algebra
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

/-- A filtered module map preserves every filtration term. -/
def FilteredModuleRespects {R : Type u} [Semiring R]
    (M N : fModule R) (f : M.M →ₗ[R] N.M) : Prop :=
  ∀ n (x : M.M), x ∈ M.filtration n → f x ∈ N.filtration n
/-- Associated graded multiplication respects the representative relation in each degree. -/
def AssociatedGradedRespects {R : Type u} [Semiring R] {A : ℕ → Type v}
    (M : aGMultip R A) (Rel : ∀ n, A n → A n → Prop) : Prop :=
  ∀ ⦃m n : ℕ⦄ ⦃x x' : A m⦄ ⦃y y' : A n⦄,
    Rel m x x' → Rel n y y' → Rel (m + n) (M.mul m n x y) (M.mul m n x' y')
/-- Augmentation degree of a sum is bounded below by the smaller input degree. -/
theorem augmentationSubadditiveSums {R : Type u} {G : Type v} [CommRing R] [Group G]
    {x y : MonoidAlgebra R G}
    (dx : augmentationAlgebraElement R G x)
    (dy : augmentationAlgebraElement R G y) :
    x + y ∈ powersAugmentationIdeal R G (min dx.1 dy.1)
  := by
  have hx : x ∈ powersAugmentationIdeal R G (min dx.1 dy.1) :=
    GroupAlgebra.augmentationPower_antitone R G (Nat.min_le_left dx.1 dy.1) dx.2.1
  have hy : y ∈ powersAugmentationIdeal R G (min dx.1 dy.1) :=
    GroupAlgebra.augmentationPower_antitone R G (Nat.min_le_right dx.1 dy.1) dy.2.1
  exact Ideal.add_mem _ hx hy
/-- Boundary maps kill syzygies generated by relators. -/
theorem foxBoundaryKills {R : Type u} [Semiring R]
    (B : rMBounda R) (x : LinearMap.ker B.map) :
    B.map x.1 = 0
  := by
  exact x.2
/-- Associated graded multiplication is independent of representatives. -/
theorem associatedWellDefined {R : Type u} [Semiring R]
    {A : ℕ → Type v} (M : aGMultip R A)
    (Rel : ∀ n, A n → A n → Prop) (hM : AssociatedGradedRespects M Rel)
    {m n : ℕ} {x x' : A m} {y y' : A n} :
    Rel m x x' → Rel n y y' →
      Rel (m + n) (M.mul m n x y) (M.mul m n x' y')
  := by
  exact fun hxx' hyy' => hM hxx' hyy'
/-- Membership in D_n is equivalent to augmentation-power membership. -/
theorem dimensionSubgroupCondition {R : Type u} {G : Type v} [CommRing R] [Group G]
    (n : ℕ) (g : G) :
    g ∈ GroupAlgebra.dSubgro R G n ↔
      (MonoidAlgebra.of R G g - 1 : MonoidAlgebra R G) ∈
        GroupAlgebra.augmentationPower R G n
  := by
  rfl
/-- Nilpotence of the augmentation ideal kills all sufficiently high layers. -/
theorem nilpotentHighLayers {R : Type u} {G : Type v}
    [CommRing R] [Group G] (N : ℕ)
    (hN : powersAugmentationIdeal R G N = ⊥) {n : ℕ} :
    N ≤ n → powersAugmentationIdeal R G n = ⊥
  := by
  intro hNn
  apply le_antisymm
  · rw [← hN]
    exact GroupAlgebra.augmentationPower_antitone R G hNn
  · exact bot_le
/-- Filtered multiplication respects degrees. -/
theorem filteredRespectsDegrees {R : Type u} {G : Type v}
    [CommRing R] [Group G] {m n : ℕ} {x y : MonoidAlgebra R G} :
    x ∈ powersAugmentationIdeal R G m → y ∈ powersAugmentationIdeal R G n →
      x * y ∈ powersAugmentationIdeal R G (m + n)
  := by
  exact fun hx hy => GroupAlgebra.mul_augmentation_add (R := R) (G := G) hx hy
/-- Augmentation powers multiply additively. -/
theorem powersMultiplyAdditively {R : Type u} {G : Type v} [CommRing R] [Group G]
    {m n : ℕ} {x y : MonoidAlgebra R G} :
    x ∈ powersAugmentationIdeal R G m → y ∈ powersAugmentationIdeal R G n →
      x * y ∈ powersAugmentationIdeal R G (m + n)
  := by
  exact fun hx hy => GroupAlgebra.mul_augmentation_add (R := R) (G := G) hx hy
/-- Controlled products add augmentation degrees. -/
theorem additiveControlledProducts {R : Type u} {G : Type v}
    [CommRing R] [Group G] {x y : MonoidAlgebra R G}
    (dx : augmentationAlgebraElement R G x)
    (dy : augmentationAlgebraElement R G y)
    (hleading : x * y ∉ powersAugmentationIdeal R G (dx.1 + dy.1 + 1)) :
    ∃ dxy : augmentationAlgebraElement R G (x * y), dxy.1 = dx.1 + dy.1
  := by
  refine ⟨⟨dx.1 + dy.1, ?_, hleading⟩, rfl⟩
  exact GroupAlgebra.mul_augmentation_add (R := R) (G := G) dx.2.1 dy.2.1

private theorem linear_ker {R : Type u} [Ring R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {P : Type w} {Q : Type w'} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {p : M →ₗ[R] P} {q : M →ₗ[R] Q}
    (hker : LinearMap.ker p ≤ LinearMap.ker q) {x y : M} (hxy : p x = p y) :
    q x = q y := by
  exact (LinearMap.sub_mem_ker_iff (f := q)).1
    (hker ((LinearMap.sub_mem_ker_iff (f := p)).2 hxy))

/-- Filtered module maps descend to associated graded modules. -/
theorem filteredInducesGraded {R : Type u} [Ring R]
    (A B : aGModule R) (f : A.source.M →ₗ[R] B.source.M)
    (hf : FilteredModuleRespects A.source B.source f) :
    ∀ n, ∃ gr : A.piece n →ₗ[R] B.piece n,
      ∀ x : A.source.filtration n,
        gr (A.projection n x) = B.projection n ⟨f x.1, hf n x.1 x.2⟩
  := by
  classical
  intro n
  let lift : A.source.filtration n →ₗ[R] B.source.filtration n :=
    { toFun := fun x => ⟨f x.1, hf n x.1 x.2⟩
      map_add' := by
        intro x y
        ext
        exact f.map_add x.1 y.1
      map_smul' := by
        intro r x
        ext
        exact f.map_smul r x.1 }
  let q : A.source.filtration n →ₗ[R] B.piece n := (B.projection n).comp lift
  have hker : LinearMap.ker (A.projection n) ≤ LinearMap.ker q := by
    intro x hx
    have hx_next : x.1 ∈ A.source.filtration (n + 1) := by
      change x ∈ Submodule.comap (Submodule.subtype (A.source.filtration n))
        (A.source.filtration (n + 1))
      simpa [aGModule.kernel_projection] using hx
    change B.projection n (lift x) = 0
    change lift x ∈ LinearMap.ker (B.projection n)
    rw [B.kernel_next n]
    change (lift x).1 ∈ B.source.filtration (n + 1)
    exact hf (n + 1) x.1 hx_next
  let sec : A.piece n → A.source.filtration n :=
    Function.surjInv (A.projection_surjective n)
  have sec_spec : Function.RightInverse sec (A.projection n) :=
    Function.rightInverse_surjInv (A.projection_surjective n)
  let gr : A.piece n →ₗ[R] B.piece n :=
    { toFun := fun y => q (sec y)
      map_add' := by
        intro y z
        have hproj :
            A.projection n (sec (y + z)) =
              A.projection n (sec y + sec z) := by
          calc
            A.projection n (sec (y + z)) = y + z := sec_spec (y + z)
            _ = A.projection n (sec y) + A.projection n (sec z) := by
              rw [sec_spec y, sec_spec z]
            _ = A.projection n (sec y + sec z) :=
              (map_add (A.projection n) (sec y) (sec z)).symm
        calc
          q (sec (y + z)) = q (sec y + sec z) :=
            linear_ker
              (R := R) (M := A.source.filtration n) (P := A.piece n) (Q := B.piece n)
              (p := A.projection n) (q := q) hker hproj
          _ = q (sec y) + q (sec z) := map_add q (sec y) (sec z)
      map_smul' := by
        intro r y
        have hproj :
            A.projection n (sec (r • y)) =
              A.projection n (r • sec y) := by
          calc
            A.projection n (sec (r • y)) = r • y := sec_spec (r • y)
            _ = r • A.projection n (sec y) := by rw [sec_spec y]
            _ = A.projection n (r • sec y) :=
              (map_smul (A.projection n) r (sec y)).symm
        calc
          q (sec (r • y)) = q (r • sec y) :=
            linear_ker
              (R := R) (M := A.source.filtration n) (P := A.piece n) (Q := B.piece n)
              (p := A.projection n) (q := q) hker hproj
          _ = r • q (sec y) := map_smul q r (sec y) }
  refine ⟨gr, ?_⟩
  intro x
  have hproj : A.projection n (sec (A.projection n x)) = A.projection n x :=
    sec_spec (A.projection n x)
  have hq :
      q (sec (A.projection n x)) = q x :=
    linear_ker
      (R := R) (M := A.source.filtration n) (P := A.piece n) (Q := B.piece n)
      (p := A.projection n) (q := q) hker hproj
  simpa [gr, q, lift] using hq

end Theorems
end Submission
