import Towers.Group.PresentationData

namespace Towers
namespace Algebra

universe u v w

/-- A bundled generated module over a semiring.  The historical item id was
`module`, but this package intentionally includes a chosen spanning set; use
`gModule` below when the more precise name matters. -/
structure module (R : Type u) [Semiring R] where
  carrier : Type v
  [addCommMonoid : AddCommMonoid carrier]
  [module' : Module R carrier]
  generators : Set carrier
  spans : Submodule.span R generators = ⊤

attribute [instance] module.addCommMonoid module.module'

/-- More precise synonym for the generated-module package. -/
abbrev gModule (R : Type u) [Semiring R] := module R

/-- A distinguished generator of a bundled module lies in the spanning submodule. -/
theorem module.generator_mem_span {R : Type u} [Semiring R] (M : module R)
    {x : M.carrier} (hx : x ∈ M.generators) :
    x ∈ Submodule.span R M.generators :=
  Submodule.subset_span hx

/-- Since the generators span, every element lies in their span. -/
theorem module.mem_span_generators {R : Type u} [Semiring R] (M : module R)
    (x : M.carrier) : x ∈ Submodule.span R M.generators := by
  rw [M.spans]
  exact Submodule.mem_top

/-- A generated module is spanned by its displayed generators. -/
theorem gModule.mem_span_generators {R : Type u} [Semiring R]
    (M : gModule R) (x : M.carrier) : x ∈ Submodule.span R M.generators :=
  module.mem_span_generators M x


/-- The syzygy module of a linear map, i.e. its kernel. -/
abbrev syzygy (R : Type u) [Semiring R] {M : Type v} {N : Type w}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) : Submodule R M :=
  LinearMap.ker f

/-- A bundled module basis, recorded by its vectors plus independence and spanning. -/
structure basis (R : Type u) [Semiring R] (M : Type v)
    [AddCommMonoid M] [Module R M] where
  index : Type w
  vec : index → M
  independent : LinearIndependent R vec
  spans : Submodule.span R (Set.range vec) = ⊤
  repr : M →ₗ[R] (index →₀ R)
  total : (index →₀ R) →ₗ[R] M
  total_single : ∀ i r, total (Finsupp.single i r) = r • vec i
  left_inverse : Function.LeftInverse total repr
  right_inverse : Function.RightInverse total repr

/-- A bundled basis gives a linear equivalence with finitely supported coordinates. -/
noncomputable def basis.linearEquivFinsupp {R : Type u} [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] (B : basis R M) :
    M ≃ₗ[R] (B.index →₀ R) where
  toLinearMap := B.repr
  invFun := B.total
  left_inv := B.left_inverse
  right_inv := B.right_inverse

@[simp] theorem basis.lin_equiv_finsuppapply {R : Type u} [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] (B : basis R M) (x : M) :
    B.linearEquivFinsupp x = B.repr x := rfl

@[simp] theorem basis.lin_equivfinsupp_symmapply {R : Type u} [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] (B : basis R M)
    (f : B.index →₀ R) : B.linearEquivFinsupp.symm f = B.total f := rfl

/-- Totaling a single coordinate is the recorded basis vector formula. -/
theorem basis.total_single_apply {R : Type u} [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] (B : basis R M)
    (i : B.index) (r : R) : B.total (Finsupp.single i r) = r • B.vec i :=
  B.total_single i r

/-- One homogeneous component of an indexed graded object. -/
abbrev homogeneousComponent (A : ℕ → Type u) (n : ℕ) : Type u := A n

/-- A leading term of a graded expansion.  The `component` field is the whole
family of homogeneous components of the underlying object; lower components of
*this family* vanish, rather than every element of lower degrees being zero. -/
structure leadingTerm (A : ℕ → Type u) where
  [zeroA : ∀ n, Zero (A n)]
  component : ∀ n, A n
  degree : ℕ
  nonzero : component degree ≠ 0
  lower_zero : ∀ m, m < degree → component m = 0

/-- The displayed leading homogeneous component. -/
def leadingTerm.term {A : ℕ → Type u} (t : leadingTerm A) : A t.degree :=
  t.component t.degree

/-- The displayed leading term is nonzero. -/
theorem leadingTerm.term_ne_zero {A : ℕ → Type u} (t : leadingTerm A) :
    (letI := t.zeroA t.degree; t.term ≠ 0) := by
  exact t.nonzero

/-- A strictly lower component of the underlying expansion is zero. -/
theorem leadingTerm.component_eqzero_ltdegree {A : ℕ → Type u} (t : leadingTerm A)
    {m : ℕ} (hm : m < t.degree) :
    (letI := t.zeroA m; t.component m = 0) := by
  exact t.lower_zero m hm

/-- The stored term is definitionally the component in the recorded degree. -/
theorem leadingTerm.term_eq_component' {A : ℕ → Type u} (t : leadingTerm A) :
    t.term = t.component t.degree := rfl

/-- Terms whose degree is strictly above a specified weight.  The degree witness
and the term now live in the same sigma component. -/
def higherErrorTerms (A : ℕ → Type u) (n : ℕ) : Type u :=
  Σ m : {m : ℕ // n < m}, A m.1


/-- A chosen `p`-operation on a type. -/
abbrev pOperation (L : Type u) : Type u := L → L

/-- A binary Lie-bracket-shaped operation. -/
abbrev lieBracket (L : Type u) : Type u := L → L → L

/-- A restricted-Lie-algebra-shaped interface.  We include the additive/module
structure and the basic bilinearity/Jacobi laws as fields; the characteristic-`p`
identities for `pmap` can be specialized by later files. -/
structure rLAlg (R : Type u) [Semiring R] where
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module' : Module R carrier]
  bracket : carrier → carrier → carrier
  pmap : carrier → carrier
  bracket_add_left : ∀ x y z, bracket (x + y) z = bracket x z + bracket y z
  bracket_add_right : ∀ x y z, bracket x (y + z) = bracket x y + bracket x z
  bracket_smul_left : ∀ (r : R) x y, bracket (r • x) y = r • bracket x y
  bracket_smul_right : ∀ (r : R) x y, bracket x (r • y) = r • bracket x y
  bracket_self : ∀ x, bracket x x = 0
  bracket_skew : ∀ x y, bracket x y = - bracket y x
  jacobi : ∀ x y z, bracket x (bracket y z) + bracket y (bracket z x) +
    bracket z (bracket x y) = 0
  restrictedPrime : ℕ
  restrictedPrime_prime : Nat.Prime restrictedPrime
  char_p : CharP R restrictedPrime
  pmap_zero : pmap 0 = 0
  pmap_smul : ∀ (r : R) x, pmap (r • x) = (r ^ restrictedPrime) • pmap x
  pmap_additive_commuting : ∀ x y, bracket x y = 0 → pmap (x + y) = pmap x + pmap y
  ad_pmap : ∀ x y, bracket (pmap x) y =
    (Nat.iterate (fun z => bracket x z) restrictedPrime) y

attribute [instance] rLAlg.addCommGroup rLAlg.module'

@[simp] theorem rLAlg.bracket_self_eqzero {R : Type u} [Semiring R]
    (L : rLAlg R) (x : L.carrier) : L.bracket x x = 0 :=
  L.bracket_self x

@[simp] theorem rLAlg.pmap_zero_eq {R : Type u} [Semiring R]
    (L : rLAlg R) : L.pmap 0 = 0 := L.pmap_zero

/-- Skew-symmetry as a rewriteable named theorem. -/
theorem rLAlg.bracket_skew' {R : Type u} [Semiring R]
    (L : rLAlg R) (x y : L.carrier) :
    L.bracket x y = - L.bracket y x := L.bracket_skew x y

/-- The recorded restricted prime is prime. -/
theorem rLAlg.prime {R : Type u} [Semiring R]
    (L : rLAlg R) : Nat.Prime L.restrictedPrime :=
  L.restrictedPrime_prime

/-- The recorded restricted prime also gives a `Fact` instance when needed for `ZMod`. -/
instance rLAlg.fact_prime {R : Type u} [Semiring R]
    (L : rLAlg R) : Fact L.restrictedPrime.Prime :=
  ⟨L.restrictedPrime_prime⟩

/-- The base semiring has the recorded characteristic. -/
theorem rLAlg.charP {R : Type u} [Semiring R]
    (L : rLAlg R) : CharP R L.restrictedPrime :=
  L.char_p

/-- Left additivity of the bracket, as a named projection. -/
theorem rLAlg.bracket_add_leftapply {R : Type u} [Semiring R]
    (L : rLAlg R) (x y z : L.carrier) :
    L.bracket (x + y) z = L.bracket x z + L.bracket y z :=
  L.bracket_add_left x y z

/-- Right additivity of the bracket, as a named projection. -/
theorem rLAlg.bracket_add_rightapply {R : Type u} [Semiring R]
    (L : rLAlg R) (x y z : L.carrier) :
    L.bracket x (y + z) = L.bracket x y + L.bracket x z :=
  L.bracket_add_right x y z

/-- Additivity of the p-map on commuting elements. -/
theorem rLAlg.pmap_add_commuting {R : Type u} [Semiring R]
    (L : rLAlg R) {x y : L.carrier} (h : L.bracket x y = 0) :
    L.pmap (x + y) = L.pmap x + L.pmap y :=
  L.pmap_additive_commuting x y h


/-- A bundled algebra intended to be the restricted enveloping algebra of a
restricted Lie algebra.  Besides the ambient algebra, it records the canonical
linear inclusion and the commutator relation; a later specialization can add the
characteristic-`p` power relation once `p` is fixed. -/
structure rEAlg (R : Type u) [CommRing R] where
  lie : rLAlg.{u, v} R
  carrier : Type w
  [ring' : Ring carrier]
  [algebra' : Algebra R carrier]
  incl : lie.carrier → carrier
  incl_injective : Function.Injective incl
  incl_add : ∀ x y, incl (x + y) = incl x + incl y
  incl_smul : ∀ (r : R) x, incl (r • x) = r • incl x
  bracket_relation : ∀ x y, incl (lie.bracket x y) = incl x * incl y - incl y * incl x
  restricted_power_relation : ∀ x, incl (lie.pmap x) = incl x ^ lie.restrictedPrime

attribute [instance] rEAlg.ring' rEAlg.algebra'

/-- The displayed Lie inclusion is injective. -/
theorem rEAlg.incl_inj {R : Type u} [CommRing R]
    (U : rEAlg R) : Function.Injective U.incl :=
  U.incl_injective

theorem rEAlg.incl_add_apply {R : Type u} [CommRing R]
    (U : rEAlg R) (x y : U.lie.carrier) :
    U.incl (x + y) = U.incl x + U.incl y := U.incl_add x y

theorem rEAlg.incl_smul_apply {R : Type u} [CommRing R]
    (U : rEAlg R) (r : R) (x : U.lie.carrier) :
    U.incl (r • x) = r • U.incl x := U.incl_smul r x

/-- The defining commutator relation in a restricted enveloping algebra. -/
theorem rEAlg.bracket_relation_apply {R : Type u} [CommRing R]
    (U : rEAlg R) (x y : U.lie.carrier) :
    U.incl (U.lie.bracket x y) = U.incl x * U.incl y - U.incl y * U.incl x :=
  U.bracket_relation x y

/-- The defining restricted-power relation in a restricted enveloping algebra. -/
theorem rEAlg.power_relation_apply {R : Type u} [CommRing R]
    (U : rEAlg R) (x : U.lie.carrier) :
    U.incl (U.lie.pmap x) = U.incl x ^ U.lie.restrictedPrime :=
  U.restricted_power_relation x


/-- A subgroup maximal among proper subgroups. -/
def maximalSubgroup (G : Type u) [Group G] (H : Subgroup G) : Prop :=
  H < ⊤ ∧ ∀ K : Subgroup G, H < K → K = ⊤

/-- An algebra homomorphism over a base semiring. -/
abbrev algebraHomomorphism (R : Type u) (A : Type v) (B : Type w)
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B] :=
  A →ₐ[R] B

/-- The augmentation map of a group algebra. -/
noncomputable abbrev augmentationMap (R : Type u) (G : Type v) [CommRing R] [Group G] :
    MonoidAlgebra R G →ₐ[R] R :=
  GroupAlgebra.augmentation R G

/-- The augmentation ideal of a group algebra. -/
noncomputable abbrev augmentationIdeal (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Ideal (MonoidAlgebra R G) :=
  GroupAlgebra.augmentationIdeal R G

/-- Dimension of a vector space, as a cardinal rank. -/
noncomputable abbrev vectorSpaceDimension (R : Type u) (V : Type v)
    [DivisionRing R] [AddCommGroup V] [Module R V] : Cardinal :=
  Module.rank R V

/-- A vector space over `𝔽_p`, used as the elementary abelian model. -/
structure eFSpace (p : ℕ) where
  [fact_prime : Fact p.Prime]
  prime : Nat.Prime p := fact_prime.out
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module' : Module (ZMod p) carrier]
  [finite' : Finite carrier]
  exponent_p : ∀ x : carrier, p • x = 0

attribute [instance] eFSpace.fact_prime
attribute [instance] eFSpace.addCommGroup
attribute [instance] eFSpace.module'
attribute [instance] eFSpace.finite'

@[simp] theorem eFSpace.exponent_apply (p : ℕ)
    (V : eFSpace.{u} p) (x : V.carrier) :
    p • x = 0 := V.exponent_p x

/-- The packaged prime witness for an elementary abelian `𝔽_p`-space. -/
theorem eFSpace.prime' (p : ℕ)
    (V : eFSpace.{u} p) : Nat.Prime p := V.prime


end Algebra
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

universe u v w x

/-- A family of vectors spans each graded degree. -/
def DegreewiseSpanning {R : Type u} [Semiring R] (M : ℕ → Type v)
    [∀ n, AddCommMonoid (M n)] [∀ n, Module R (M n)]
    (S : ∀ n, Set (M n)) : Prop :=
  ∀ n, Submodule.span R (S n) = ⊤
/-- A higher-weight term has degree strictly above the displayed cutoff. -/
theorem higherAboveCutoff {A : ℕ → Type u} (n : ℕ) :
    ∀ e : higherErrorTerms A n, n < e.1.1
  := by
  intro e
  exact e.1.2

end Theorems
end Towers
