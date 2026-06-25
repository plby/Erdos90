import Submission.Group.HallBasic.Polynomial
import Submission.Group.LowerCentralStrong



noncomputable section

namespace Submission
namespace TBluepr

universe u v

/--
A family of finitely supported vectors is linearly independent if each vector
has its own coefficient-one pivot and vanishes at every other pivot.
-/
theorem linear_independent_pivot
    (R : Type u) [Ring R]
    {ι : Type v}
    {κ : Type*}
    (vector : ι → κ →₀ R)
    (pivot : ι → κ)
    (hpivot : ∀ i, vector i (pivot i) = 1)
    (hoffDiagonal : ∀ i j, i ≠ j → vector j (pivot i) = 0) :
    LinearIndependent R vector := by
  apply linearIndependent_iff'.2
  intro s coefficient hsum i hi
  have hcoefficient :=
    congrArg (fun p : κ →₀ R => p (pivot i)) hsum
  change (∑ j ∈ s, coefficient j • vector j) (pivot i) = 0 at hcoefficient
  rw [Finset.sum_apply', Finset.sum_eq_single i] at hcoefficient
  · simpa [hpivot i] using hcoefficient
  · intro j hj hji
    simp [hoffDiagonal i j hji.symm]
  · exact fun hnotMem => (hnotMem hi).elim

/--
The same pivot criterion with diagonal coefficients allowed to be either
`1` or `-1`.  This is the form suited to leading-word Hall arguments.
-/
theorem finsupp_linear_pivot
    (R : Type u) [Ring R]
    {ι : Type v}
    {κ : Type*}
    (vector : ι → κ →₀ R)
    (pivot : ι → κ)
    (hpivot : ∀ i, vector i (pivot i) = 1 ∨ vector i (pivot i) = -1)
    (hoffDiagonal : ∀ i j, i ≠ j → vector j (pivot i) = 0) :
    LinearIndependent R vector := by
  apply linearIndependent_iff'.2
  intro s coefficient hsum i hi
  have hcoefficient :=
    congrArg (fun p : κ →₀ R => p (pivot i)) hsum
  change (∑ j ∈ s, coefficient j • vector j) (pivot i) = 0 at hcoefficient
  rw [Finset.sum_apply', Finset.sum_eq_single i] at hcoefficient
  · rcases hpivot i with hpivot | hpivot
    · simpa [hpivot] using hcoefficient
    · simpa [hpivot] using hcoefficient
  · intro j hj hji
    simp [hoffDiagonal i j hji.symm]
  · exact fun hnotMem => (hnotMem hi).elim

end TBluepr

namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/--
The forward-reading word of leaves of a Hall tree.  In low weights it is
already a pivot word for the recursive bracket polynomial.  From weight three
onward repeated leaves can collide, so the eventual Hall triangularity theorem
needs a refined standard word.
-/
def foliageWord : HallTree α → FreeMonoid α
  | atom a => FreeMonoid.of a
  | commutator u v => u.foliageWord * v.foliageWord

@[simp] theorem foliageWord_atom (a : α) :
    (atom a).foliageWord = FreeMonoid.of a :=
  rfl

@[simp] theorem foliageWord_commutator (u v : HallTree α) :
    (commutator u v).foliageWord = u.foliageWord * v.foliageWord :=
  rfl

/-- The foliage word has the same length as the Hall tree's weight. -/
@[simp] theorem foliageWord_length (w : HallTree α) :
    w.foliageWord.length = w.weight := by
  induction w with
  | atom a => simp [foliageWord]
  | commutator u v ihu ihv =>
      simp [foliageWord, ihu, ihv]

/-- A weight-one Hall tree is an atom. -/
theorem atom_one
    {w : HallTree α}
    (hweight : w.weight = 1) :
    ∃ a : α, w = atom a :=
  weight_eq_iff.mp hweight

/-- A weight-two Hall tree is a bracket of two atoms. -/
theorem commutator_atoms_two
    {w : HallTree α}
    (hweight : w.weight = 2) :
    ∃ a b : α, w = commutator (atom a) (atom b) := by
  cases w with
  | atom a =>
      simp at hweight
  | commutator u v =>
      have huPos := u.weight_pos
      have hvPos := v.weight_pos
      have huWeight : u.weight = 1 := by
        simp only [weight_commutator] at hweight
        omega
      have hvWeight : v.weight = 1 := by
        simp only [weight_commutator] at hweight
        omega
      obtain ⟨a, rfl⟩ := atom_one huWeight
      obtain ⟨b, rfl⟩ := atom_one hvWeight
      exact ⟨a, b, rfl⟩

theorem free_monoid
    {a b c d : α} :
    FreeMonoid.of a * FreeMonoid.of b =
        FreeMonoid.of c * FreeMonoid.of d ↔
      a = c ∧ b = d := by
  constructor
  · intro h
    have hlist := congrArg FreeMonoid.toList h
    simpa using hlist
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem free_monoid_swap
    {a b : α}
    (hab : a ≠ b) :
    FreeMonoid.of a * FreeMonoid.of b ≠
      FreeMonoid.of b * FreeMonoid.of a := by
  intro h
  exact hab (free_monoid.mp h).1

theorem free_monoid_mul
    {a b c d e f : α} :
    FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of c) =
        FreeMonoid.of d * (FreeMonoid.of e * FreeMonoid.of f) ↔
      a = d ∧ b = e ∧ c = f := by
  constructor
  · intro h
    have hlist := congrArg FreeMonoid.toList h
    simpa using hlist
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- The foliage coefficient of a weight-one Hall polynomial is one. -/
theorem associative_foliage_weight
    (R : Type*) [CommRing R]
    (w : HallTree α)
    (hweight : w.weight = 1) :
    w.associativeWordPolynomial R w.foliageWord = 1 := by
  obtain ⟨a, rfl⟩ := atom_one hweight
  simp

/--
A weight-one Hall polynomial vanishes at the foliage word of any distinct
weight-one Hall tree.
-/
theorem associative_foliage_one
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (huWeight : u.weight = 1)
    (hvWeight : v.weight = 1)
    (huv : u ≠ v) :
    v.associativeWordPolynomial R u.foliageWord = 0 := by
  obtain ⟨a, rfl⟩ := atom_one huWeight
  obtain ⟨b, rfl⟩ := atom_one hvWeight
  have hab : a ≠ b := by
    intro hab
    apply huv
    simp [hab]
  rw [associative_word_atom, foliageWord_atom,
    Finsupp.single_eq_of_ne (FreeMonoid.of_injective.ne hab)]

/-- The foliage coefficient of a basic weight-two Hall polynomial is one. -/
theorem associative_foliage_basic
    (R : Type*) [CommRing R] [Encodable α]
    (w : HallTree α)
    (hbasic : w.IsBasic)
    (hweight : w.weight = 2) :
    w.associativeWordPolynomial R w.foliageWord = 1 := by
  obtain ⟨a, b, rfl⟩ := commutator_atoms_two hweight
  have hba : atom b < atom a := (isBasic_commutator _ _).mp hbasic |>.2.2.1
  have hab : a ≠ b := by
    intro hab
    subst b
    exact (lt_irrefl _ hba)
  simp only [associative_word_commutator,
    associative_word_atom, foliageWord_commutator, foliageWord_atom,
    MonoidAlgebra.single_mul_single]
  change
    (Finsupp.single (FreeMonoid.of a * FreeMonoid.of b) (1 * 1 : R))
          (FreeMonoid.of a * FreeMonoid.of b) -
        (Finsupp.single (FreeMonoid.of b * FreeMonoid.of a) (1 * 1 : R))
          (FreeMonoid.of a * FreeMonoid.of b) =
      1
  rw [Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (free_monoid_swap hab)]
  simp

/--
A basic weight-two Hall polynomial vanishes at the foliage word of every
distinct basic weight-two Hall tree.
-/
theorem associative_foliage_two
    (R : Type*) [CommRing R] [Encodable α]
    (u v : HallTree α)
    (huBasic : u.IsBasic)
    (hvBasic : v.IsBasic)
    (huWeight : u.weight = 2)
    (hvWeight : v.weight = 2)
    (huv : u ≠ v) :
    v.associativeWordPolynomial R u.foliageWord = 0 := by
  obtain ⟨a, b, rfl⟩ := commutator_atoms_two huWeight
  obtain ⟨c, d, rfl⟩ := commutator_atoms_two hvWeight
  have hba : atom b < atom a := (isBasic_commutator _ _).mp huBasic |>.2.2.1
  have hdc : atom d < atom c := (isBasic_commutator _ _).mp hvBasic |>.2.2.1
  have hforward :
      FreeMonoid.of a * FreeMonoid.of b ≠
        FreeMonoid.of c * FreeMonoid.of d := by
    intro h
    rcases free_monoid.mp h with ⟨rfl, rfl⟩
    exact huv rfl
  have hreverse :
      FreeMonoid.of a * FreeMonoid.of b ≠
        FreeMonoid.of d * FreeMonoid.of c := by
    intro h
    rcases free_monoid.mp h with ⟨rfl, rfl⟩
    exact (lt_asymm hba hdc)
  simp only [associative_word_commutator,
    associative_word_atom, foliageWord_commutator, foliageWord_atom,
    MonoidAlgebra.single_mul_single]
  change
    (Finsupp.single (FreeMonoid.of c * FreeMonoid.of d) (1 * 1 : R))
          (FreeMonoid.of a * FreeMonoid.of b) -
        (Finsupp.single (FreeMonoid.of d * FreeMonoid.of c) (1 * 1 : R))
          (FreeMonoid.of a * FreeMonoid.of b) =
      0
  rw [Finsupp.single_eq_of_ne hforward,
    Finsupp.single_eq_of_ne hreverse]
  simp

/--
Raw foliage ceases to be a unit-coefficient pivot in weight three: the
polynomial of `[[a,b],a]` has foliage coefficient `2`.
-/
theorem associative_foliage_atom
    (R : Type*) [CommRing R]
    {a b : α}
    (hab : a ≠ b) :
    (commutator (commutator (atom a) (atom b)) (atom a)).associativeWordPolynomial R
        (commutator (commutator (atom a) (atom b)) (atom a)).foliageWord =
      2 := by
  have hleft :
      FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of a) ≠
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of a) := by
    intro h
    exact hab (free_monoid_mul.mp h).1
  have hmiddle :
      FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of a) ≠
        FreeMonoid.of a * (FreeMonoid.of a * FreeMonoid.of b) := by
    intro h
    exact hab (free_monoid_mul.mp h).2.1.symm
  simp only [associative_word_commutator,
    associative_word_atom, foliageWord_commutator, foliageWord_atom,
    mul_sub, sub_mul, MonoidAlgebra.single_mul_single, mul_assoc]
  change
    ((Finsupp.single
          (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of a))
          (1 * (1 * 1) : R))
        (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of a)) -
      (Finsupp.single
          (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of a))
          (1 * (1 * 1) : R))
        (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of a))) -
        ((Finsupp.single
            (FreeMonoid.of a * (FreeMonoid.of a * FreeMonoid.of b))
            (1 * (1 * 1) : R))
          (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of a)) -
        (Finsupp.single
            (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of a))
            (1 * (1 * 1) : R))
          (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of a))) =
      2
  rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hleft,
    Finsupp.single_eq_of_ne hmiddle]
  ring

section FiniteAlphabet

variable [Fintype α] [DecidableEq α] [Encodable α]

/--
Whenever foliage pivot equations hold, they imply independence of the indexed
Hall polynomials in that fixed weight.  They hold in weights one and two below;
higher weights need a refined standard-word triangularity argument.
-/
theorem indexed_foliage_pivots
    (R : Type*) [CommRing R]
    (r : ℕ)
    (hpivot :
      ∀ i : BasicIndex (α := α) r,
        (indexedBasicTree i).associativeWordPolynomial R
            (indexedBasicTree i).foliageWord =
          1)
    (hoffDiagonal :
      ∀ i j : BasicIndex (α := α) r, i ≠ j →
        (indexedBasicTree j).associativeWordPolynomial R
            (indexedBasicTree i).foliageWord =
          0) :
    LinearIndependent R fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).associativeRepWeight R
        (indexed_tree_weight i) := by
  apply LinearIndependent.of_comp
    (Finsupp.supported R R {word : FreeMonoid α | word.length = r}).subtype
  exact
    linear_independent_pivot R
      (fun i : BasicIndex (α := α) r =>
        (indexedBasicTree i).associativeWordPolynomial R)
      (fun i : BasicIndex (α := α) r =>
        (indexedBasicTree i).foliageWord)
      hpivot hoffDiagonal

/--
Foliage pivot equations imply independence of the indexed Hall classes in
the free-group lower-central associated graded.
-/
theorem indexed_layers_pivots
    {r : ℕ}
    (hr : 0 < r)
    (hpivot :
      ∀ i : BasicIndex (α := α) r,
        (indexedBasicTree i).associativeWordPolynomial ℤ
            (indexedBasicTree i).foliageWord =
          1)
    (hoffDiagonal :
      ∀ i j : BasicIndex (α := α) r, i ≠ j →
        (indexedBasicTree j).associativeWordPolynomial ℤ
            (indexedBasicTree i).foliageWord =
          0) :
    LinearIndependent ℤ fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) :=
  free_independent_associative
    hr
    (indexedBasicTree (α := α) (r := r))
    indexed_tree_weight
    (indexed_foliage_pivots
      ℤ r hpivot hoffDiagonal)

/-- The indexed weight-one Hall polynomials are linearly independent. -/
theorem indexed_homogeneous_independent
    (R : Type*) [CommRing R] :
    LinearIndependent R fun i : BasicIndex (α := α) 1 =>
      (indexedBasicTree i).associativeRepWeight R
        (indexed_tree_weight i) := by
  apply LinearIndependent.of_comp
    (Finsupp.supported R R {word : FreeMonoid α | word.length = 1}).subtype
  apply linear_independent_pivot R
    (pivot := fun i : BasicIndex (α := α) 1 =>
      (indexedBasicTree i).foliageWord)
  · intro i
    exact
      associative_foliage_weight
        R (indexedBasicTree i) (indexed_tree_weight i)
  · intro i j hij
    exact
      associative_foliage_one
        R (indexedBasicTree i) (indexedBasicTree j)
        (indexed_tree_weight i) (indexed_tree_weight j)
        (fun h => hij (indexed_tree_injective h))

/-- The indexed weight-two Hall polynomials are linearly independent. -/
theorem indexed_associative_independent
    (R : Type*) [CommRing R] :
    LinearIndependent R fun i : BasicIndex (α := α) 2 =>
      (indexedBasicTree i).associativeRepWeight R
        (indexed_tree_weight i) := by
  apply LinearIndependent.of_comp
    (Finsupp.supported R R {word : FreeMonoid α | word.length = 2}).subtype
  apply linear_independent_pivot R
    (pivot := fun i : BasicIndex (α := α) 2 =>
      (indexedBasicTree i).foliageWord)
  · intro i
    exact
      associative_foliage_basic
        R (indexedBasicTree i) (indexed_tree i)
        (indexed_tree_weight i)
  · intro i j hij
    exact
      associative_foliage_two
        R (indexedBasicTree i) (indexedBasicTree j)
        (indexed_tree i) (indexed_tree j)
        (indexed_tree_weight i) (indexed_tree_weight j)
        (fun h => hij (indexed_tree_injective h))

/--
The indexed weight-one Hall classes in the free-group lower-central associated
graded are linearly independent.
-/
theorem indexed_linear_independent :
    LinearIndependent ℤ fun i : BasicIndex (α := α) 1 =>
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) :=
  free_independent_associative
    (by omega)
    (indexedBasicTree (α := α) (r := 1))
    indexed_tree_weight
    (indexed_homogeneous_independent
      ℤ)

/--
The indexed weight-two Hall classes in the free-group lower-central associated
graded are linearly independent.
-/
theorem indexed_free_independent :
    LinearIndependent ℤ fun i : BasicIndex (α := α) 2 =>
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) :=
  free_independent_associative
    (by omega)
    (indexedBasicTree (α := α) (r := 2))
    indexed_tree_weight
    (indexed_associative_independent
      ℤ)

end FiniteAlphabet

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
A fixed-weight signed standard-word certificate for Hall polynomials.  This is
the triangularity input needed by the Magnus route to Hall independence.
-/
structure SSPivots
    (R : Type*) [CommRing R]
    (r : ℕ) where
  standardWord : BasicIndex (α := α) r → FreeMonoid α
  diagonal :
    ∀ i,
      (indexedBasicTree i).associativeWordPolynomial R (standardWord i) = 1 ∨
        (indexedBasicTree i).associativeWordPolynomial R (standardWord i) = -1
  offDiagonal :
    ∀ i j, i ≠ j →
      (indexedBasicTree j).associativeWordPolynomial R (standardWord i) = 0

/--
A signed standard-word certificate gives linear independence of the indexed
Hall polynomials in its fixed homogeneous degree.
-/
theorem SSPivots.assocw_polyh_weigh
    (R : Type*) [CommRing R]
    {r : ℕ}
    (P : SSPivots (α := α) R r) :
    LinearIndependent R fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).associativeRepWeight R
        (indexed_tree_weight i) := by
  apply LinearIndependent.of_comp
    (Finsupp.supported R R {word : FreeMonoid α | word.length = r}).subtype
  exact
    finsupp_linear_pivot R
      (fun i : BasicIndex (α := α) r =>
        (indexedBasicTree i).associativeWordPolynomial R)
      P.standardWord P.diagonal P.offDiagonal

/--
A signed standard-word certificate transfers through the Magnus map to linear
independence in the corresponding free-group lower-central layer.
-/
theorem SSPivots.freegr_lowec_weigh
    {r : ℕ}
    (P : SSPivots (α := α) ℤ r)
    (hr : 0 < r) :
    LinearIndependent ℤ fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) :=
  free_independent_associative
    hr
    (indexedBasicTree (α := α) (r := r))
    indexed_tree_weight
    (P.assocw_polyh_weigh ℤ)

/--
The additional spanning input required to upgrade standard-word independence
to a basis of the free-group lower-central layer.
-/
structure FBInput
    (r : ℕ) where
  pivots : SSPivots (α := α) ℤ r
  span_eq_top :
    Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) r =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) =
      ⊤

/--
Signed standard-word triangularity plus lower-central spanning constructs the
fixed-weight Hall basis.
-/
noncomputable def FBInput.basis
    {r : ℕ}
    (P : FBInput (α := α) r)
    (hr : 0 < r) :
    Module.Basis (BasicIndex (α := α) r) ℤ
      (Additive
        (LowerGradedLayer (FreeGroup α) (r - 1))) :=
  Module.Basis.mk
    (P.pivots.freegr_lowec_weigh hr)
    (by rw [P.span_eq_top])

/--
All-weight signed standard-word triangularity, packaged weight by weight.  A
recursive Hall argument should construct this object.
-/
structure SSSystem
    (R : Type*) [CommRing R] where
  pivots : ∀ r, SSPivots (α := α) R r

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/-- The multiplicative degree-one lower-central class map on free-group words. -/
def lowerCentralHom :
    FreeGroup α →*
      LowerGradedLayer (FreeGroup α) 0 :=
  (QuotientGroup.mk'
    ((Subgroup.lowerCentralSeries (FreeGroup α) 1).subgroupOf
      (Subgroup.lowerCentralSeries (FreeGroup α) 0))).comp
    ((MonoidHom.id (FreeGroup α)).codRestrict
      (Subgroup.lowerCentralSeries (FreeGroup α) 0)
      (fun _ => by simp [Subgroup.lowerCentralSeries_zero]))

/-- The degree-one lower-central class represented by a free-group word. -/
def weightCentralClass
    (w : FreeGroup α) :
    Additive
      (LowerGradedLayer (FreeGroup α) 0) :=
  Additive.ofMul (lowerCentralHom w)

@[simp]
theorem weight_lower_class :
    weightCentralClass (α := α) 1 = 0 := by
  simp [weightCentralClass]

@[simp]
theorem lower_central_mul
    (u v : FreeGroup α) :
    weightCentralClass (u * v) =
      weightCentralClass u + weightCentralClass v := by
  simp [weightCentralClass]

@[simp]
theorem lower_central_inv
    (u : FreeGroup α) :
    weightCentralClass u⁻¹ =
      -weightCentralClass u := by
  simp [weightCentralClass]

/-- Reindexing a Hall class is insensitive to a proof-preserving tree equality. -/
theorem free_lower_congr
    {w v : HallTree α}
    {n : ℕ}
    (h : w = v)
    (hw : w.weight = n)
    (hv : v.weight = n) :
    w.freeLowerWeight hw =
      v.freeLowerWeight hv := by
  subst v
  rfl

/-- The degree-one class of a free generator is the Hall class of its atom. -/
theorem weight_central_class
    (a : α) :
    weightCentralClass (FreeGroup.of a) =
      (atom a).freeCentralLayer := by
  rfl

variable [Fintype α] [DecidableEq α] [Encodable α]

/-- A free generator gives the degree-one Hall class indexed by its atom. -/
theorem weight_lower_span
    (a : α) :
    weightCentralClass (FreeGroup.of a) ∈
      Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 1 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) := by
  obtain ⟨i, hi⟩ := indexed_tree_atom (α := α) a
  apply Submodule.subset_span
  refine ⟨i, ?_⟩
  rw [weight_central_class]
  exact
    (free_lower_congr hi
      (indexed_tree_weight i) (by rfl)).trans
      (show
          (atom a).freeLowerWeight (by rfl) =
            (atom a).freeCentralLayer
        from rfl)

/--
The weight-one Hall classes span the degree-one free-group lower-central
associated-graded layer.
-/
theorem indexed_span_top :
    Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 1 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) =
      ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective
      ((Subgroup.lowerCentralSeries (FreeGroup α) 1).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) 0)) z.toMul
  change Additive.ofMul z.toMul ∈
    Submodule.span ℤ
      (Set.range fun i : BasicIndex (α := α) 1 =>
        (indexedBasicTree i).freeLowerWeight
          (indexed_tree_weight i))
  rw [← hg]
  change
    weightCentralClass (g : FreeGroup α) ∈
      Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 1 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i))
  induction (g : FreeGroup α) using FreeGroup.induction_on with
  | C1 =>
      simp
  | of a =>
      exact weight_lower_span a
  | inv_of a ha =>
      simpa using
        (Submodule.neg_mem _ ha)
  | mul u v hu hv =>
      simpa using
        (Submodule.add_mem _ hu hv)

/-- Foliage words give signed standard-word pivots in weight one. -/
def basisStandardPivots :
    SSPivots (α := α) ℤ 1 where
  standardWord i := (indexedBasicTree i).foliageWord
  diagonal i :=
    Or.inl
      (associative_foliage_weight
        ℤ (indexedBasicTree i) (indexed_tree_weight i))
  offDiagonal i j hij :=
    associative_foliage_one
      ℤ (indexedBasicTree i) (indexedBasicTree j)
      (indexed_tree_weight i) (indexed_tree_weight j)
      (fun h => hij (indexed_tree_injective h))

/-- The weight-one Hall classes form a basis of the free-group graded layer. -/
def weightBasisInput :
    FBInput (α := α) 1 where
  pivots := basisStandardPivots
  span_eq_top :=
    indexed_span_top

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/--
Every basic Hall tree of weight three has the shape `[[a,b],c]`, with the
usual Hall inequalities `b < a` and `b ≤ c`.
-/
theorem commutator_atoms_three
    [Encodable α]
    {w : HallTree α}
    (hbasic : w.IsBasic)
    (hweight : w.weight = 3) :
    ∃ a b c : α,
      w = commutator (commutator (atom a) (atom b)) (atom c) ∧
        atom b < atom a ∧ atom b ≤ atom c := by
  cases w with
  | atom a =>
      simp at hweight
  | commutator u v =>
      rcases (isBasic_commutator u v).mp hbasic with
        ⟨huBasic, _hvBasic, hvu, hadmissible⟩
      have huPos := u.weight_pos
      have hvPos := v.weight_pos
      have huWeight : u.weight = 2 := by
        by_contra huWeightNe
        have huWeightOne : u.weight = 1 := by
          simp only [weight_commutator] at hweight
          omega
        have hvWeightTwo : v.weight = 2 := by
          simp only [weight_commutator] at hweight
          omega
        have huv : u < v :=
          lt_weight_lt (huWeightOne.symm ▸ hvWeightTwo.symm ▸ by omega)
        exact (lt_asymm hvu huv)
      have hvWeight : v.weight = 1 := by
        simp only [weight_commutator] at hweight
        omega
      obtain ⟨a, b, rfl⟩ := commutator_atoms_two huWeight
      obtain ⟨c, rfl⟩ := atom_one hvWeight
      exact
        ⟨a, b, c, rfl,
          (isBasic_commutator (atom a) (atom b)).mp huBasic |>.2.2.1,
          by simpa using hadmissible⟩

/--
The refined standard word for weight-three Hall trees.  For a basic tree
`[[a,b],c]`, the smallest expansion word is `bba` when `b = c`, and `bac`
otherwise.  Both have signed-unit coefficient.
-/
noncomputable def weightStandardWord (w : HallTree α) : FreeMonoid α := by
  classical
  exact match w with
    | commutator (commutator (atom a) (atom b)) (atom c) =>
        if b = c then
          FreeMonoid.of c * (FreeMonoid.of b * FreeMonoid.of a)
        else
          FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)
    | w => w.foliageWord

@[simp] theorem standard_commutator_atoms
    [DecidableEq α]
    (a b c : α) :
    (commutator (commutator (atom a) (atom b)) (atom c)).weightStandardWord =
      if b = c then
        FreeMonoid.of c * (FreeMonoid.of b * FreeMonoid.of a)
      else
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c) :=
  by
    classical
    by_cases hbc : b = c <;> simp [weightStandardWord, hbc]

/-- The explicit four-term expansion of a weight-three left-normed bracket. -/
theorem associative_commutator_atoms
    (R : Type*) [CommRing R]
    (a b c : α) :
    (commutator (commutator (atom a) (atom b)) (atom c)).associativeWordPolynomial R =
      MonoidAlgebra.single
          (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of c)) 1 -
        MonoidAlgebra.single
          (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)) 1 -
        (MonoidAlgebra.single
            (FreeMonoid.of c * (FreeMonoid.of a * FreeMonoid.of b)) 1 -
          MonoidAlgebra.single
            (FreeMonoid.of c * (FreeMonoid.of b * FreeMonoid.of a)) 1) := by
  simp [mul_sub, sub_mul, mul_assoc]

private theorem standard_signed_coefficient
    (R : Type*) [CommRing R] [Encodable α]
    (a b c : α)
    (hba : atom b < atom a) :
    (commutator (commutator (atom a) (atom b)) (atom c)).associativeWordPolynomial R
        (commutator (commutator (atom a) (atom b)) (atom c)).weightStandardWord =
      1 ∨
    (commutator (commutator (atom a) (atom b)) (atom c)).associativeWordPolynomial R
        (commutator (commutator (atom a) (atom b)) (atom c)).weightStandardWord =
      -1 := by
  classical
  have hab : a ≠ b := by
    intro hab
    subst b
    exact (lt_irrefl _ hba)
  by_cases hbc : b = c
  · subst c
    left
    have h₁ :
        FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a) ≠
          FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of b) := by
      intro h
      exact hab (free_monoid_mul.mp h).1.symm
    have h₂ :
        FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a) ≠
          FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of b) := by
      intro h
      exact hab (free_monoid_mul.mp h).2.1.symm
    rw [associative_commutator_atoms,
      standard_commutator_atoms, if_pos rfl]
    change
      (Finsupp.single
            (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of b)) (1 : R))
          (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a)) -
        (Finsupp.single
            (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of b)) (1 : R))
          (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a)) -
        ((Finsupp.single
              (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of b)) (1 : R))
            (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a)) -
          (Finsupp.single
              (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a)) (1 : R))
            (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a))) =
        1
    rw [Finsupp.single_eq_of_ne h₁, Finsupp.single_eq_of_ne h₂,
      Finsupp.single_eq_same]
    ring
  · right
    have h₁ :
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c) ≠
          FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of c) := by
      intro h
      exact hab (free_monoid_mul.mp h).1.symm
    have h₃ :
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c) ≠
          FreeMonoid.of c * (FreeMonoid.of a * FreeMonoid.of b) := by
      intro h
      exact hbc (free_monoid_mul.mp h).1
    have h₄ :
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c) ≠
          FreeMonoid.of c * (FreeMonoid.of b * FreeMonoid.of a) := by
      intro h
      exact hbc (free_monoid_mul.mp h).1
    rw [associative_commutator_atoms,
      standard_commutator_atoms, if_neg hbc]
    change
      (Finsupp.single
            (FreeMonoid.of a * (FreeMonoid.of b * FreeMonoid.of c)) (1 : R))
          (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)) -
        (Finsupp.single
            (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)) (1 : R))
          (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)) -
        ((Finsupp.single
              (FreeMonoid.of c * (FreeMonoid.of a * FreeMonoid.of b)) (1 : R))
            (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)) -
          (Finsupp.single
              (FreeMonoid.of c * (FreeMonoid.of b * FreeMonoid.of a)) (1 : R))
            (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c))) =
        -1
    rw [Finsupp.single_eq_of_ne h₁, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne h₃, Finsupp.single_eq_of_ne h₄]
    ring

/--
The refined weight-three standard word has signed-unit coefficient in every
basic Hall polynomial.
-/
theorem associative_standard_signed
    (R : Type*) [CommRing R] [Encodable α]
    (w : HallTree α)
    (hbasic : w.IsBasic)
    (hweight : w.weight = 3) :
    w.associativeWordPolynomial R w.weightStandardWord = 1 ∨
      w.associativeWordPolynomial R w.weightStandardWord = -1 := by
  obtain ⟨a, b, c, rfl, hba, _hbc⟩ :=
    commutator_atoms_three hbasic hweight
  exact standard_signed_coefficient R a b c hba

private theorem standard_off_diagonal
    (R : Type*) [CommRing R] [Encodable α]
    (a b c d e f : α)
    (hba : atom b < atom a)
    (hbc : atom b ≤ atom c)
    (hed : atom e < atom d)
    (hef : atom e ≤ atom f)
    (hne :
      commutator (commutator (atom a) (atom b)) (atom c) ≠
        commutator (commutator (atom d) (atom e)) (atom f)) :
    (commutator (commutator (atom d) (atom e)) (atom f)).associativeWordPolynomial R
        (commutator (commutator (atom a) (atom b)) (atom c)).weightStandardWord =
      0 := by
  classical
  by_cases hbcEq : b = c
  · subst c
    have h₁ :
        FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a) ≠
          FreeMonoid.of d * (FreeMonoid.of e * FreeMonoid.of f) := by
      intro h
      rcases free_monoid_mul.mp h with
        ⟨rfl, rfl, rfl⟩
      exact (lt_irrefl _ hed)
    have h₂ :
        FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a) ≠
          FreeMonoid.of e * (FreeMonoid.of d * FreeMonoid.of f) := by
      intro h
      rcases free_monoid_mul.mp h with
        ⟨rfl, rfl, rfl⟩
      exact (lt_irrefl _ hed)
    have h₃ :
        FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a) ≠
          FreeMonoid.of f * (FreeMonoid.of d * FreeMonoid.of e) := by
      intro h
      rcases free_monoid_mul.mp h with
        ⟨rfl, rfl, rfl⟩
      exact (lt_asymm hba hed)
    have h₄ :
        FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a) ≠
          FreeMonoid.of f * (FreeMonoid.of e * FreeMonoid.of d) := by
      intro h
      rcases free_monoid_mul.mp h with
        ⟨rfl, rfl, rfl⟩
      exact hne rfl
    rw [associative_commutator_atoms,
      standard_commutator_atoms, if_pos rfl]
    change
      (Finsupp.single
            (FreeMonoid.of d * (FreeMonoid.of e * FreeMonoid.of f)) (1 : R))
          (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a)) -
        (Finsupp.single
            (FreeMonoid.of e * (FreeMonoid.of d * FreeMonoid.of f)) (1 : R))
          (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a)) -
        ((Finsupp.single
              (FreeMonoid.of f * (FreeMonoid.of d * FreeMonoid.of e)) (1 : R))
            (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a)) -
          (Finsupp.single
              (FreeMonoid.of f * (FreeMonoid.of e * FreeMonoid.of d)) (1 : R))
            (FreeMonoid.of b * (FreeMonoid.of b * FreeMonoid.of a))) =
        0
    rw [Finsupp.single_eq_of_ne h₁, Finsupp.single_eq_of_ne h₂,
      Finsupp.single_eq_of_ne h₃, Finsupp.single_eq_of_ne h₄]
    ring
  · have h₁ :
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c) ≠
          FreeMonoid.of d * (FreeMonoid.of e * FreeMonoid.of f) := by
      intro h
      rcases free_monoid_mul.mp h with
        ⟨rfl, rfl, rfl⟩
      exact (lt_asymm hba hed)
    have h₂ :
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c) ≠
          FreeMonoid.of e * (FreeMonoid.of d * FreeMonoid.of f) := by
      intro h
      rcases free_monoid_mul.mp h with
        ⟨rfl, rfl, rfl⟩
      exact hne rfl
    have h₃ :
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c) ≠
          FreeMonoid.of f * (FreeMonoid.of d * FreeMonoid.of e) := by
      intro h
      rcases free_monoid_mul.mp h with
        ⟨rfl, rfl, rfl⟩
      have heq : atom b = atom c := le_antisymm hbc hef
      exact hbcEq (HallTree.atom.inj heq)
    have h₄ :
        FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c) ≠
          FreeMonoid.of f * (FreeMonoid.of e * FreeMonoid.of d) := by
      intro h
      rcases free_monoid_mul.mp h with
        ⟨rfl, rfl, rfl⟩
      exact (not_le_of_gt hba) hef
    rw [associative_commutator_atoms,
      standard_commutator_atoms, if_neg hbcEq]
    change
      (Finsupp.single
            (FreeMonoid.of d * (FreeMonoid.of e * FreeMonoid.of f)) (1 : R))
          (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)) -
        (Finsupp.single
            (FreeMonoid.of e * (FreeMonoid.of d * FreeMonoid.of f)) (1 : R))
          (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)) -
        ((Finsupp.single
              (FreeMonoid.of f * (FreeMonoid.of d * FreeMonoid.of e)) (1 : R))
            (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c)) -
          (Finsupp.single
              (FreeMonoid.of f * (FreeMonoid.of e * FreeMonoid.of d)) (1 : R))
            (FreeMonoid.of b * (FreeMonoid.of a * FreeMonoid.of c))) =
        0
    rw [Finsupp.single_eq_of_ne h₁, Finsupp.single_eq_of_ne h₂,
      Finsupp.single_eq_of_ne h₃, Finsupp.single_eq_of_ne h₄]
    ring

/--
A basic weight-three Hall polynomial vanishes at the refined standard word of
every distinct basic weight-three Hall tree.
-/
theorem associative_standard_ne
    (R : Type*) [CommRing R] [Encodable α]
    (u v : HallTree α)
    (huBasic : u.IsBasic)
    (hvBasic : v.IsBasic)
    (huWeight : u.weight = 3)
    (hvWeight : v.weight = 3)
    (huv : u ≠ v) :
    v.associativeWordPolynomial R u.weightStandardWord = 0 := by
  obtain ⟨a, b, c, rfl, hba, hbc⟩ :=
    commutator_atoms_three huBasic huWeight
  obtain ⟨d, e, f, rfl, hed, hef⟩ :=
    commutator_atoms_three hvBasic hvWeight
  exact standard_off_diagonal R a b c d e f hba hbc hed hef huv

section FiniteAlphabet

variable [Fintype α] [DecidableEq α] [Encodable α]

/-- The refined standard words give a signed pivot packet in weight three. -/
noncomputable def signedStandardPivots
    (R : Type*) [CommRing R] :
    SSPivots (α := α) R 3 where
  standardWord i := (indexedBasicTree i).weightStandardWord
  diagonal i :=
    associative_standard_signed
      R (indexedBasicTree i) (indexed_tree i)
      (indexed_tree_weight i)
  offDiagonal i j hij :=
    associative_standard_ne
      R (indexedBasicTree i) (indexedBasicTree j)
      (indexed_tree i) (indexed_tree j)
      (indexed_tree_weight i) (indexed_tree_weight j)
      (fun h => hij (indexed_tree_injective h))

/-- The indexed weight-three Hall polynomials are linearly independent. -/
theorem indexed_rep_independent
    (R : Type*) [CommRing R] :
    LinearIndependent R fun i : BasicIndex (α := α) 3 =>
      (indexedBasicTree i).associativeRepWeight R
        (indexed_tree_weight i) :=
  SSPivots.assocw_polyh_weigh
    R (signedStandardPivots R)

/--
The indexed weight-three Hall classes in the free-group lower-central
associated graded are linearly independent.
-/
theorem indexed_tree_independent :
    LinearIndependent ℤ fun i : BasicIndex (α := α) 3 =>
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) :=
  (signedStandardPivots ℤ).freegr_lowec_weigh
    (by omega)

end FiniteAlphabet

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
Signed standard-word data through a finite weight bound.  This is the
finite-stage form of `SSSystem` suited to recursive
construction.
-/
structure SSUp
    (R : Type*) [CommRing R]
    (n : ℕ) where
  pivots : ∀ r, r ≤ n → SSPivots (α := α) R r

/-- Restrict an all-weight signed standard-word system to a finite stage. -/
noncomputable def SSSystem.toUpTo
    (R : Type*) [CommRing R]
    (P : SSSystem (α := α) R)
    (n : ℕ) :
    SSUp (α := α) R n where
  pivots r _ := P.pivots r

/-- Extend a finite-stage signed standard-word system by one weight. -/
noncomputable def SSUp.succ
    (R : Type*) [CommRing R]
    {n : ℕ}
    (P : SSUp (α := α) R n)
    (next : SSPivots (α := α) R (n + 1)) :
    SSUp (α := α) R (n + 1) where
  pivots r hr := by
    by_cases h : r ≤ n
    · exact P.pivots r h
    · have : r = n + 1 := by omega
      simpa only [this] using next

/-- There are no canonical basic Hall indices of weight zero. -/
theorem basic_index_empty :
    IsEmpty (BasicIndex (α := α) 0) := by
  rw [BasicIndex, basic_trees_zero]
  simpa only [List.length_nil] using (inferInstance : IsEmpty (Fin 0))

instance instEmptyZero :
    IsEmpty (BasicIndex (α := α) 0) :=
  basic_index_empty

/-- The vacuous signed-pivot packet in weight zero. -/
noncomputable def weightStandardPivots
    (R : Type*) [CommRing R] :
    SSPivots (α := α) R 0 where
  standardWord i := isEmptyElim i
  diagonal i := isEmptyElim i
  offDiagonal i := isEmptyElim i

/-- Raw foliage gives the signed-pivot packet in weight one. -/
noncomputable def standardWordPivots
    (R : Type*) [CommRing R] :
    SSPivots (α := α) R 1 where
  standardWord i := (indexedBasicTree i).foliageWord
  diagonal i :=
    Or.inl
      (associative_foliage_weight
        R (indexedBasicTree i) (indexed_tree_weight i))
  offDiagonal i j hij :=
    associative_foliage_one
      R (indexedBasicTree i) (indexedBasicTree j)
      (indexed_tree_weight i) (indexed_tree_weight j)
      (fun h => hij (indexed_tree_injective h))

/-- Raw foliage gives the signed-pivot packet in weight two. -/
noncomputable def twoStandardPivots
    (R : Type*) [CommRing R] :
    SSPivots (α := α) R 2 where
  standardWord i := (indexedBasicTree i).foliageWord
  diagonal i :=
    Or.inl
      (associative_foliage_basic
        R (indexedBasicTree i) (indexed_tree i)
        (indexed_tree_weight i))
  offDiagonal i j hij :=
    associative_foliage_two
      R (indexedBasicTree i) (indexedBasicTree j)
      (indexed_tree i) (indexed_tree j)
      (indexed_tree_weight i) (indexed_tree_weight j)
      (fun h => hij (indexed_tree_injective h))

/--
The verified low-weight signed standard-word system: vacuous in weight zero,
raw foliage in weights one and two, and the refined word in weight three.
-/
noncomputable def standardSystemUp
    (R : Type*) [CommRing R] :
    SSUp (α := α) R 3 where
  pivots r hr := by
    interval_cases r
    · exact weightStandardPivots R
    · exact standardWordPivots R
    · exact twoStandardPivots R
    · exact signedStandardPivots R

/--
The indexed Hall polynomials are linearly independent uniformly in every
verified weight through three.
-/
theorem indexed_polynomials_independent
    (R : Type*) [CommRing R]
    {r : ℕ}
    (hr : r ≤ 3) :
    LinearIndependent R fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).associativeRepWeight R
        (indexed_tree_weight i) :=
  SSPivots.assocw_polyh_weigh
    R ((standardSystemUp R).pivots r hr)

/--
The indexed Hall classes are linearly independent in the free-group
lower-central layer uniformly in every positive verified weight through three.
-/
theorem indexed_layers_independent
    {r : ℕ}
    (hrPos : 0 < r)
    (hr : r ≤ 3) :
    LinearIndependent ℤ fun i : BasicIndex (α := α) r =>
      (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) :=
  SSPivots.freegr_lowec_weigh
    ((standardSystemUp ℤ).pivots r hr) hrPos

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr
open scoped commutatorElement

universe u

variable {α : Type u}

/-- The multiplicative degree-two lower-central class map on `γ₂`. -/
def weightTwoHom :
    Subgroup.lowerCentralSeries (FreeGroup α) 1 →*
      LowerGradedLayer (FreeGroup α) 1 :=
  QuotientGroup.mk'
    ((Subgroup.lowerCentralSeries (FreeGroup α) 2).subgroupOf
      (Subgroup.lowerCentralSeries (FreeGroup α) 1))

/-- The degree-two lower-central class represented by an element of `γ₂`. -/
def weightTwoClass
    (w : Subgroup.lowerCentralSeries (FreeGroup α) 1) :
    Additive
      (LowerGradedLayer (FreeGroup α) 1) :=
  Additive.ofMul (weightTwoHom w)

@[simp]
theorem weight_two_lower :
    weightTwoClass (α := α) 1 = 0 := by
  change
    Additive.ofMul (weightTwoHom (α := α) 1) =
      (0 : Additive
        (LowerGradedLayer (FreeGroup α) 1))
  rw [map_one]
  rfl

@[simp]
theorem weight_two_mul
    (u v : Subgroup.lowerCentralSeries (FreeGroup α) 1) :
    weightTwoClass (u * v) =
      weightTwoClass u + weightTwoClass v := by
  change
    Additive.ofMul (weightTwoHom (u * v)) =
      Additive.ofMul (weightTwoHom u) +
        Additive.ofMul (weightTwoHom v)
  rw [map_mul]
  rfl

@[simp]
theorem weight_two_inv
    (u : Subgroup.lowerCentralSeries (FreeGroup α) 1) :
    weightTwoClass u⁻¹ =
      -weightTwoClass u := by
  change
    Additive.ofMul (weightTwoHom u⁻¹) =
      -Additive.ofMul (weightTwoHom u)
  rw [map_inv]
  rfl

/-- An ordinary free-group commutator, represented in `γ₂`. -/
def weightCommutatorRep
    (u v : FreeGroup α) :
    Subgroup.lowerCentralSeries (FreeGroup α) 1 :=
  ⟨⁅u, v⁆, by
    rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet u v)⟩

/-- The degree-two lower-central class of an ordinary free-group commutator. -/
def weightCommutatorClass
    (u v : FreeGroup α) :
    Additive
      (LowerGradedLayer (FreeGroup α) 1) :=
  weightTwoClass (weightCommutatorRep u v)

@[simp]
theorem weight_two_left
    (v : FreeGroup α) :
    weightCommutatorClass (1 : FreeGroup α) v = 0 := by
  change weightTwoClass (weightCommutatorRep 1 v) = 0
  rw [show
    weightCommutatorRep (1 : FreeGroup α) v = 1 by
      apply Subtype.ext
      exact commutatorElement_one_left v]
  exact weight_two_lower

@[simp]
theorem weight_two_right
    (u : FreeGroup α) :
    weightCommutatorClass u (1 : FreeGroup α) = 0 := by
  change weightTwoClass (weightCommutatorRep u 1) = 0
  rw [show
    weightCommutatorRep u (1 : FreeGroup α) = 1 by
      apply Subtype.ext
      exact commutatorElement_one_right u]
  exact weight_two_lower

/-- Conjugating a representative in `γ₂` does not change its class modulo `γ₃`. -/
theorem lower_central_conj
    (x : FreeGroup α)
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1) :
    weightTwoClass
        ⟨x * (c : FreeGroup α) * x⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries (FreeGroup α) 1).Normal).conj_mem
              (c : FreeGroup α) c.property x⟩ =
      weightTwoClass c := by
  change
    weightTwoHom
        ⟨x * (c : FreeGroup α) * x⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries (FreeGroup α) 1).Normal).conj_mem
              (c : FreeGroup α) c.property x⟩ =
      weightTwoHom c
  apply (QuotientGroup.eq_iff_div_mem).2
  change x * (c : FreeGroup α) * x⁻¹ / (c : FreeGroup α) ∈
    Subgroup.lowerCentralSeries (FreeGroup α) 2
  rw [div_eq_mul_inv]
  exact
    lower_commutator_succ 0 1
      (Subgroup.commutator_mem_commutator (by simp) c.property)

/-- Modulo `γ₃`, commutator classes are additive in their left input. -/
theorem weight_commutator_left
    (u v w : FreeGroup α) :
    weightCommutatorClass (u * v) w =
      weightCommutatorClass u w + weightCommutatorClass v w := by
  change
    weightTwoClass (weightCommutatorRep (u * v) w) =
      weightTwoClass (weightCommutatorRep u w) +
        weightTwoClass (weightCommutatorRep v w)
  rw [show
    weightCommutatorRep (u * v) w =
        ⟨u * (weightCommutatorRep v w : FreeGroup α) * u⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries (FreeGroup α) 1).Normal).conj_mem
              (weightCommutatorRep v w : FreeGroup α)
              (weightCommutatorRep v w).property u⟩ *
          weightCommutatorRep u w by
      apply Subtype.ext
      exact element_mul_left u v w]
  rw [weight_two_mul, lower_central_conj]
  exact add_comm _ _

/-- Modulo `γ₃`, commutator classes are additive in their right input. -/
theorem weight_commutator_right
    (u v w : FreeGroup α) :
    weightCommutatorClass u (v * w) =
      weightCommutatorClass u v + weightCommutatorClass u w := by
  change
    weightTwoClass (weightCommutatorRep u (v * w)) =
      weightTwoClass (weightCommutatorRep u v) +
        weightTwoClass (weightCommutatorRep u w)
  rw [show
    weightCommutatorRep u (v * w) =
        weightCommutatorRep u v *
          ⟨v * (weightCommutatorRep u w : FreeGroup α) * v⁻¹,
            (inferInstance :
              (Subgroup.lowerCentralSeries (FreeGroup α) 1).Normal).conj_mem
                (weightCommutatorRep u w : FreeGroup α)
                (weightCommutatorRep u w).property v⟩ by
      apply Subtype.ext
      simpa only [mul_assoc] using element_mul_right u v w]
  rw [weight_two_mul, lower_central_conj]

@[simp]
theorem weight_inv_left
    (u v : FreeGroup α) :
    weightCommutatorClass u⁻¹ v =
      -weightCommutatorClass u v := by
  have h := weight_commutator_left u⁻¹ u v
  rw [inv_mul_cancel, weight_two_left] at h
  calc
    weightCommutatorClass u⁻¹ v =
        (weightCommutatorClass u⁻¹ v +
          weightCommutatorClass u v) +
            (-weightCommutatorClass u v) := by simp
    _ = -weightCommutatorClass u v := by rw [← h, zero_add]

@[simp]
theorem weight_inv_right
    (u v : FreeGroup α) :
    weightCommutatorClass u v⁻¹ =
      -weightCommutatorClass u v := by
  have h := weight_commutator_right u v⁻¹ v
  rw [inv_mul_cancel, weight_two_right] at h
  calc
    weightCommutatorClass u v⁻¹ =
        (weightCommutatorClass u v⁻¹ +
          weightCommutatorClass u v) +
            (-weightCommutatorClass u v) := by simp
    _ = -weightCommutatorClass u v := by rw [← h, zero_add]

/-- Degree-two commutator classes are skew-symmetric. -/
theorem weight_commutator_swap
    (u v : FreeGroup α) :
    weightCommutatorClass v u =
      -weightCommutatorClass u v := by
  change
    weightTwoClass (weightCommutatorRep v u) =
      -weightTwoClass (weightCommutatorRep u v)
  rw [← weight_two_inv]
  congr 1
  apply Subtype.ext
  exact (commutatorElement_inv u v).symm

@[simp]
theorem weight_commutator_self
    (u : FreeGroup α) :
    weightCommutatorClass u u = 0 := by
  change weightTwoClass (weightCommutatorRep u u) = 0
  rw [show
    weightCommutatorRep u u = 1 by
      apply Subtype.ext
      exact commutatorElement_self u]
  exact weight_two_lower

variable [Fintype α] [DecidableEq α] [Encodable α]

/-- An ordered pair of distinct free generators gives a basic Hall class. -/
theorem weight_commutator_span
    (a b : α)
    (hba : atom b < atom a) :
    weightCommutatorClass (FreeGroup.of a) (FreeGroup.of b) ∈
      Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 2 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) := by
  obtain ⟨i, hi⟩ :=
    indexed_basic_tree
      (basic_commutator_admissible
        (isBasic_atom a) (isBasic_atom b) hba trivial)
      (show (commutator (atom a) (atom b)).weight = 2 by simp)
  apply Submodule.subset_span
  refine ⟨i, ?_⟩
  change
    (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) =
      weightCommutatorClass (FreeGroup.of a) (FreeGroup.of b)
  calc
    (indexedBasicTree i).freeLowerWeight
          (indexed_tree_weight i) =
        (commutator (atom a) (atom b)).freeLowerWeight
          (by simp) :=
      free_lower_congr hi
        (indexed_tree_weight i) (by simp)
    _ = weightCommutatorClass (FreeGroup.of a) (FreeGroup.of b) := by
      rfl

/-- Every commutator class of two free generators belongs to the weight-two Hall span. -/
theorem commutator_class_span
    (a b : α) :
    weightCommutatorClass (FreeGroup.of a) (FreeGroup.of b) ∈
      Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 2 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) := by
  rcases lt_trichotomy (atom b) (atom a) with hba | hba | hab
  · exact weight_commutator_span a b hba
  · cases hba
    simp
  · rw [weight_commutator_swap]
    exact
      Submodule.neg_mem _
        (weight_commutator_span b a hab)

/-- Every ordinary free-group commutator class belongs to the weight-two Hall span. -/
theorem weight_two_span
    (u v : FreeGroup α) :
    weightCommutatorClass u v ∈
      Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 2 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) := by
  induction u using FreeGroup.induction_on with
  | C1 =>
      simp
  | of a =>
      induction v using FreeGroup.induction_on with
      | C1 =>
          simp
      | of b =>
          exact commutator_class_span a b
      | inv_of v hv =>
          simpa using Submodule.neg_mem _ hv
      | mul v w hv hw =>
          simpa [weight_commutator_right] using
            Submodule.add_mem _ hv hw
  | inv_of u hu =>
      simpa using Submodule.neg_mem _ hu
  | mul u w hu hw =>
      simpa [weight_commutator_left] using
        Submodule.add_mem _ hu hw

/--
Every class represented by an element of `γ₂` belongs to the weight-two Hall
span.
-/
theorem lower_central_span
    (g : Subgroup.lowerCentralSeries (FreeGroup α) 1) :
    weightTwoClass g ∈
      Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 2 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) := by
  have hg :
      (g : FreeGroup α) ∈
        Subgroup.closure (commutatorSet (FreeGroup α)) := by
    simpa [Subgroup.lowerCentralSeries_one, commutator_eq_closure] using g.property
  refine Subgroup.closure_induction
    (k := commutatorSet (FreeGroup α))
    (p := fun x hx =>
      weightTwoClass
        ⟨x, by
          rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
          exact hx⟩ ∈
        Submodule.span ℤ
          (Set.range fun i : BasicIndex (α := α) 2 =>
            (indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i)))
    ?_ ?_ ?_ ?_ hg
  · intro x hx
    rw [commutatorSet_def] at hx
    rcases hx with ⟨u, v, rfl⟩
    exact weight_two_span u v
  · change weightTwoClass
      (1 : Subgroup.lowerCentralSeries (FreeGroup α) 1) ∈
        Submodule.span ℤ
          (Set.range fun i : BasicIndex (α := α) 2 =>
            (indexedBasicTree i).freeLowerWeight
              (indexed_tree_weight i))
    simp
  · intro x y hx hy hxm hym
    simpa using
      (Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 2 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i))).add_mem hxm hym
  · intro x hx hxm
    rw [show
      (⟨x⁻¹, by
          rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
          exact Subgroup.inv_mem _ hx⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 1) =
        (⟨x, by
          rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
          exact hx⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 1)⁻¹ by
          rfl,
      weight_two_inv]
    exact
      (Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 2 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i))).neg_mem hxm

/--
The weight-two Hall classes span the degree-two free-group lower-central
associated-graded layer.
-/
theorem indexed_free_top :
    Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 2 =>
          (indexedBasicTree i).freeLowerWeight
            (indexed_tree_weight i)) =
      ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective
      ((Subgroup.lowerCentralSeries (FreeGroup α) 2).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) 1)) z.toMul
  change Additive.ofMul z.toMul ∈
    Submodule.span ℤ
      (Set.range fun i : BasicIndex (α := α) 2 =>
        (indexedBasicTree i).freeLowerWeight
          (indexed_tree_weight i))
  rw [← hg]
  change weightTwoClass g ∈
    Submodule.span ℤ
      (Set.range fun i : BasicIndex (α := α) 2 =>
        (indexedBasicTree i).freeLowerWeight
          (indexed_tree_weight i))
  exact lower_central_span g

/-- The weight-two Hall classes form a basis of the free-group graded layer. -/
def lowerBasisInput :
    FBInput (α := α) 2 where
  pivots := twoStandardPivots ℤ
  span_eq_top :=
    indexed_free_top

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr
open scoped commutatorElement

universe u

variable {α : Type u}

/-- The multiplicative degree-three lower-central class map on `γ₃`. -/
def weightLowerHom :
    Subgroup.lowerCentralSeries (FreeGroup α) 2 →*
      LowerGradedLayer (FreeGroup α) 2 :=
  QuotientGroup.mk'
    ((Subgroup.lowerCentralSeries (FreeGroup α) 3).subgroupOf
      (Subgroup.lowerCentralSeries (FreeGroup α) 2))

/-- The degree-three lower-central class represented by an element of `γ₃`. -/
def weightLowerClass
    (w : Subgroup.lowerCentralSeries (FreeGroup α) 2) :
    Additive
      (LowerGradedLayer (FreeGroup α) 2) :=
  Additive.ofMul (weightLowerHom w)

@[simp]
theorem weight_lower_central :
    weightLowerClass (α := α) 1 = 0 := by
  change
    Additive.ofMul (weightLowerHom (α := α) 1) =
      (0 : Additive
        (LowerGradedLayer (FreeGroup α) 2))
  rw [map_one]
  rfl

@[simp]
theorem weight_lower_mul
    (u v : Subgroup.lowerCentralSeries (FreeGroup α) 2) :
    weightLowerClass (u * v) =
      weightLowerClass u + weightLowerClass v := by
  change
    Additive.ofMul (weightLowerHom (u * v)) =
      Additive.ofMul (weightLowerHom u) +
        Additive.ofMul (weightLowerHom v)
  rw [map_mul]
  rfl

@[simp]
theorem weight_lower_inv
    (u : Subgroup.lowerCentralSeries (FreeGroup α) 2) :
    weightLowerClass u⁻¹ =
      -weightLowerClass u := by
  change
    Additive.ofMul (weightLowerHom u⁻¹) =
      -Additive.ofMul (weightLowerHom u)
  rw [map_inv]
  rfl

/-- A commutator of an element of `γ₂` with an arbitrary free-group word,
represented in `γ₃`. -/
def weightBracketRep
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x : FreeGroup α) :
    Subgroup.lowerCentralSeries (FreeGroup α) 2 :=
  ⟨⁅(c : FreeGroup α), x⁆,
    lower_commutator_succ 1 0
      (Subgroup.commutator_mem_commutator c.property (by simp))⟩

/-- The degree-three class of the bracket of an element of `γ₂` with an arbitrary word. -/
def weightBracketClass
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x : FreeGroup α) :
    Additive
      (LowerGradedLayer (FreeGroup α) 2) :=
  weightLowerClass (weightBracketRep c x)

@[simp]
theorem weight_three_bracket
    (x : FreeGroup α) :
    weightBracketClass
        (1 : Subgroup.lowerCentralSeries (FreeGroup α) 1) x =
      0 := by
  change weightLowerClass (weightBracketRep 1 x) = 0
  rw [show
    weightBracketRep (1 : Subgroup.lowerCentralSeries (FreeGroup α) 1) x = 1 by
      apply Subtype.ext
      exact commutatorElement_one_left x]
  exact weight_lower_central

@[simp]
theorem three_bracket_right
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1) :
    weightBracketClass c (1 : FreeGroup α) = 0 := by
  change weightLowerClass (weightBracketRep c 1) = 0
  rw [show
    weightBracketRep c (1 : FreeGroup α) = 1 by
      apply Subtype.ext
      change ⁅(c : FreeGroup α), (1 : FreeGroup α)⁆ = 1
      exact commutatorElement_one_right (c : FreeGroup α)]
  exact weight_lower_central

/-- Conjugating a representative in `γ₃` does not change its class modulo `γ₄`. -/
theorem weight_lower_conj
    (x : FreeGroup α)
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 2) :
    weightLowerClass
        ⟨x * (c : FreeGroup α) * x⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries (FreeGroup α) 2).Normal).conj_mem
              (c : FreeGroup α) c.property x⟩ =
      weightLowerClass c := by
  change
    weightLowerHom
        ⟨x * (c : FreeGroup α) * x⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries (FreeGroup α) 2).Normal).conj_mem
              (c : FreeGroup α) c.property x⟩ =
      weightLowerHom c
  apply (QuotientGroup.eq_iff_div_mem).2
  change x * (c : FreeGroup α) * x⁻¹ / (c : FreeGroup α) ∈
    Subgroup.lowerCentralSeries (FreeGroup α) 3
  rw [div_eq_mul_inv]
  exact
    lower_commutator_succ 0 2
      (Subgroup.commutator_mem_commutator (by simp) c.property)

/-- Modulo `γ₄`, degree-three brackets are additive in their `γ₂` input. -/
theorem three_bracket_left
    (c d : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x : FreeGroup α) :
    weightBracketClass (c * d) x =
      weightBracketClass c x + weightBracketClass d x := by
  change
    weightLowerClass (weightBracketRep (c * d) x) =
      weightLowerClass (weightBracketRep c x) +
        weightLowerClass (weightBracketRep d x)
  rw [show
    weightBracketRep (c * d) x =
        ⟨(c : FreeGroup α) *
              (weightBracketRep d x : FreeGroup α) *
              (c : FreeGroup α)⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries (FreeGroup α) 2).Normal).conj_mem
              (weightBracketRep d x : FreeGroup α)
              (weightBracketRep d x).property c⟩ *
          weightBracketRep c x by
      apply Subtype.ext
      exact
        element_mul_left (c : FreeGroup α) (d : FreeGroup α) x]
  rw [weight_lower_mul, weight_lower_conj]
  exact add_comm _ _

/-- Modulo `γ₄`, degree-three brackets are additive in their free-group input. -/
theorem weight_bracket_right
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x y : FreeGroup α) :
    weightBracketClass c (x * y) =
      weightBracketClass c x + weightBracketClass c y := by
  change
    weightLowerClass (weightBracketRep c (x * y)) =
      weightLowerClass (weightBracketRep c x) +
        weightLowerClass (weightBracketRep c y)
  rw [show
    weightBracketRep c (x * y) =
        weightBracketRep c x *
          ⟨x * (weightBracketRep c y : FreeGroup α) * x⁻¹,
            (inferInstance :
              (Subgroup.lowerCentralSeries (FreeGroup α) 2).Normal).conj_mem
                (weightBracketRep c y : FreeGroup α)
                (weightBracketRep c y).property x⟩ by
      apply Subtype.ext
      simpa only [mul_assoc] using
        element_mul_right (c : FreeGroup α) x y]
  rw [weight_lower_mul, weight_lower_conj]

/-- Bracketing an element of `γ₃` with an arbitrary word vanishes modulo `γ₄`. -/
theorem bracket_series_two
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (hc : (c : FreeGroup α) ∈ Subgroup.lowerCentralSeries (FreeGroup α) 2)
    (x : FreeGroup α) :
    weightBracketClass c x = 0 := by
  change
    Additive.ofMul
        (weightLowerHom (weightBracketRep c x)) =
      0
  change weightLowerHom (weightBracketRep c x) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  change ⁅(c : FreeGroup α), x⁆ ∈ Subgroup.lowerCentralSeries (FreeGroup α) 3
  exact
    lower_commutator_succ 2 0
      (Subgroup.commutator_mem_commutator hc (by simp))

/--
The degree-three bracket depends only on the degree-two class of its left
input.
-/
theorem bracket_congr_inv
    (c d : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x : FreeGroup α)
    (hcd :
      (c : FreeGroup α) * (d : FreeGroup α)⁻¹ ∈
        Subgroup.lowerCentralSeries (FreeGroup α) 2) :
    weightBracketClass c x =
      weightBracketClass d x := by
  let e : Subgroup.lowerCentralSeries (FreeGroup α) 1 :=
    ⟨(c : FreeGroup α) * (d : FreeGroup α)⁻¹,
      Subgroup.lowerCentralSeries_antitone (show 1 ≤ 2 by omega) hcd⟩
  have hc : c = e * d := by
    apply Subtype.ext
    change
      (c : FreeGroup α) =
        ((c : FreeGroup α) * (d : FreeGroup α)⁻¹) * (d : FreeGroup α)
    group
  rw [hc, three_bracket_left,
    bracket_series_two e hcd,
    zero_add]

/-- Conjugating the `γ₂` input does not change its degree-three bracket class. -/
theorem weight_bracket_left
    (u : FreeGroup α)
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x : FreeGroup α) :
    weightBracketClass
        ⟨u * (c : FreeGroup α) * u⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries (FreeGroup α) 1).Normal).conj_mem
              (c : FreeGroup α) c.property u⟩
        x =
      weightBracketClass c x := by
  apply
    bracket_congr_inv
  change u * (c : FreeGroup α) * u⁻¹ * (c : FreeGroup α)⁻¹ ∈
    Subgroup.lowerCentralSeries (FreeGroup α) 2
  exact
    lower_commutator_succ 0 1
      (Subgroup.commutator_mem_commutator (by simp) c.property)

@[simp]
theorem bracket_class_inv
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x : FreeGroup α) :
    weightBracketClass c⁻¹ x =
      -weightBracketClass c x := by
  have h := three_bracket_left c⁻¹ c x
  rw [inv_mul_cancel, weight_three_bracket] at h
  calc
    weightBracketClass c⁻¹ x =
        (weightBracketClass c⁻¹ x + weightBracketClass c x) +
          (-weightBracketClass c x) := by simp
    _ = -weightBracketClass c x := by rw [← h, zero_add]

@[simp]
theorem weight_bracket_inv
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x : FreeGroup α) :
    weightBracketClass c x⁻¹ =
      -weightBracketClass c x := by
  have h := weight_bracket_right c x⁻¹ x
  rw [inv_mul_cancel, three_bracket_right] at h
  calc
    weightBracketClass c x⁻¹ =
        (weightBracketClass c x⁻¹ + weightBracketClass c x) +
          (-weightBracketClass c x) := by simp
    _ = -weightBracketClass c x := by rw [← h, zero_add]

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr
open scoped commutatorElement

universe u

variable {α : Type u}

/-- The representative in `γ₃` of the left-normed triple commutator `[[u,v],w]`. -/
def weightTripleRep
    (u v w : FreeGroup α) :
    Subgroup.lowerCentralSeries (FreeGroup α) 2 :=
  weightBracketRep (weightCommutatorRep u v) w

/-- The degree-three class represented by the left-normed triple commutator `[[u,v],w]`. -/
def weightTripleClass
    (u v w : FreeGroup α) :
    Additive
      (LowerGradedLayer (FreeGroup α) 2) :=
  weightLowerClass (weightTripleRep u v w)

/--
The rearranged Hall-Witt identity used by Mathlib's proof of the Three
Subgroups Lemma.
-/
theorem commutator_witt_rearranged
    (x y z : FreeGroup α) :
    ⁅z, ⁅x, y⁆⁆ =
      x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ *
        y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ := by
  simp [commutatorElement_def, mul_assoc]

@[simp]
theorem triple_one_first
    (v w : FreeGroup α) :
    weightTripleClass (1 : FreeGroup α) v w = 0 := by
  rw [weightTripleClass, weightTripleRep, show
    weightCommutatorRep (1 : FreeGroup α) v = 1 by
      apply Subtype.ext
      exact commutatorElement_one_left v]
  exact weight_three_bracket w

@[simp]
theorem triple_one_second
    (u w : FreeGroup α) :
    weightTripleClass u (1 : FreeGroup α) w = 0 := by
  rw [weightTripleClass, weightTripleRep, show
    weightCommutatorRep u (1 : FreeGroup α) = 1 by
      apply Subtype.ext
      exact commutatorElement_one_right u]
  exact weight_three_bracket w

@[simp]
theorem triple_one_third
    (u v : FreeGroup α) :
    weightTripleClass u v (1 : FreeGroup α) = 0 :=
  three_bracket_right (weightCommutatorRep u v)

/-- Modulo `γ₄`, left-normed triple commutators are additive in their first input. -/
theorem three_triple_first
    (u v w x : FreeGroup α) :
    weightTripleClass (u * v) w x =
      weightTripleClass u w x + weightTripleClass v w x := by
  change
    weightBracketClass (weightCommutatorRep (u * v) w) x =
      weightBracketClass (weightCommutatorRep u w) x +
        weightBracketClass (weightCommutatorRep v w) x
  rw [show
    weightCommutatorRep (u * v) w =
        ⟨u * (weightCommutatorRep v w : FreeGroup α) * u⁻¹,
          (inferInstance :
            (Subgroup.lowerCentralSeries (FreeGroup α) 1).Normal).conj_mem
              (weightCommutatorRep v w : FreeGroup α)
              (weightCommutatorRep v w).property u⟩ *
          weightCommutatorRep u w by
      apply Subtype.ext
      exact element_mul_left u v w]
  rw [three_bracket_left, weight_bracket_left]
  exact add_comm _ _

/-- Modulo `γ₄`, left-normed triple commutators are additive in their second input. -/
theorem three_triple_second
    (u v w x : FreeGroup α) :
    weightTripleClass u (v * w) x =
      weightTripleClass u v x + weightTripleClass u w x := by
  change
    weightBracketClass (weightCommutatorRep u (v * w)) x =
      weightBracketClass (weightCommutatorRep u v) x +
        weightBracketClass (weightCommutatorRep u w) x
  rw [show
    weightCommutatorRep u (v * w) =
        weightCommutatorRep u v *
          ⟨v * (weightCommutatorRep u w : FreeGroup α) * v⁻¹,
            (inferInstance :
              (Subgroup.lowerCentralSeries (FreeGroup α) 1).Normal).conj_mem
                (weightCommutatorRep u w : FreeGroup α)
                (weightCommutatorRep u w).property v⟩ by
      apply Subtype.ext
      simpa only [mul_assoc] using element_mul_right u v w]
  rw [three_bracket_left, weight_bracket_left]

/-- Modulo `γ₄`, left-normed triple commutators are additive in their third input. -/
theorem three_triple_third
    (u v w x : FreeGroup α) :
    weightTripleClass u v (w * x) =
      weightTripleClass u v w + weightTripleClass u v x :=
  weight_bracket_right (weightCommutatorRep u v) w x

@[simp]
theorem weight_triple_first
    (u v w : FreeGroup α) :
    weightTripleClass u⁻¹ v w =
      -weightTripleClass u v w := by
  have h := three_triple_first u⁻¹ u v w
  rw [inv_mul_cancel, triple_one_first] at h
  calc
    weightTripleClass u⁻¹ v w =
        (weightTripleClass u⁻¹ v w + weightTripleClass u v w) +
          (-weightTripleClass u v w) := by simp
    _ = -weightTripleClass u v w := by rw [← h, zero_add]

@[simp]
theorem weight_triple_second
    (u v w : FreeGroup α) :
    weightTripleClass u v⁻¹ w =
      -weightTripleClass u v w := by
  have h := three_triple_second u v⁻¹ v w
  rw [inv_mul_cancel, triple_one_second] at h
  calc
    weightTripleClass u v⁻¹ w =
        (weightTripleClass u v⁻¹ w + weightTripleClass u v w) +
          (-weightTripleClass u v w) := by simp
    _ = -weightTripleClass u v w := by rw [← h, zero_add]

@[simp]
theorem weight_triple_third
    (u v w : FreeGroup α) :
    weightTripleClass u v w⁻¹ =
      -weightTripleClass u v w :=
  weight_bracket_inv (weightCommutatorRep u v) w

/-- Swapping the first two entries negates a left-normed degree-three triple class. -/
theorem swap_first_second
    (u v w : FreeGroup α) :
    weightTripleClass v u w =
      -weightTripleClass u v w := by
  change
    weightBracketClass (weightCommutatorRep v u) w =
      -weightBracketClass (weightCommutatorRep u v) w
  rw [← bracket_class_inv]
  congr 1
  apply Subtype.ext
  exact (commutatorElement_inv u v).symm

@[simp]
theorem triple_self_second
    (u w : FreeGroup α) :
    weightTripleClass u u w = 0 := by
  change weightBracketClass (weightCommutatorRep u u) w = 0
  rw [show
    weightCommutatorRep u u = 1 by
      apply Subtype.ext
      exact commutatorElement_self u]
  exact weight_three_bracket w

/-- The degree-three associated-graded triple classes satisfy the Jacobi identity. -/
theorem weight_triple_jacobi
    (x y z : FreeGroup α) :
    weightTripleClass x y z +
          weightTripleClass y z x +
        weightTripleClass z x y =
      0 := by
  let A : Subgroup.lowerCentralSeries (FreeGroup α) 2 :=
    weightTripleRep z⁻¹ x⁻¹ y
  let B : Subgroup.lowerCentralSeries (FreeGroup α) 2 :=
    weightTripleRep y⁻¹ z x⁻¹
  let Az : Subgroup.lowerCentralSeries (FreeGroup α) 2 :=
    ⟨z * (A : FreeGroup α) * z⁻¹,
      (inferInstance :
        (Subgroup.lowerCentralSeries (FreeGroup α) 2).Normal).conj_mem
          (A : FreeGroup α) A.property z⟩
  let By : Subgroup.lowerCentralSeries (FreeGroup α) 2 :=
    ⟨y * (B : FreeGroup α) * y⁻¹,
      (inferInstance :
        (Subgroup.lowerCentralSeries (FreeGroup α) 2).Normal).conj_mem
          (B : FreeGroup α) B.property y⟩
  let Cx : Subgroup.lowerCentralSeries (FreeGroup α) 2 :=
    ⟨x * ((Az * By : Subgroup.lowerCentralSeries (FreeGroup α) 2) : FreeGroup α) * x⁻¹,
      (inferInstance :
        (Subgroup.lowerCentralSeries (FreeGroup α) 2).Normal).conj_mem
          ((Az * By : Subgroup.lowerCentralSeries (FreeGroup α) 2) : FreeGroup α)
          (Az * By).property x⟩
  have hrep : (weightTripleRep x y z)⁻¹ = Cx := by
    apply Subtype.ext
    change
      ⁅⁅x, y⁆, z⁆⁻¹ =
        x * (z * ⁅⁅z⁻¹, x⁻¹⁆, y⁆ * z⁻¹ *
          (y * ⁅⁅y⁻¹, z⁆, x⁻¹⁆ * y⁻¹)) * x⁻¹
    calc
      ⁅⁅x, y⁆, z⁆⁻¹ = ⁅z, ⁅x, y⁆⁆ := commutatorElement_inv _ _
      _ =
          x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ *
            y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹ :=
        commutator_witt_rearranged x y z
      _ =
          x * (z * ⁅⁅z⁻¹, x⁻¹⁆, y⁆ * z⁻¹ *
            (y * ⁅⁅y⁻¹, z⁆, x⁻¹⁆ * y⁻¹)) * x⁻¹ := by
        rw [commutatorElement_inv y ⁅z⁻¹, x⁻¹⁆,
          commutatorElement_inv x⁻¹ ⁅y⁻¹, z⁆]
        group
  have hneg :
      -weightTripleClass x y z =
        weightTripleClass z x y + weightTripleClass y z x := by
    calc
      -weightTripleClass x y z =
          weightLowerClass (weightTripleRep x y z)⁻¹ := by
        rw [weightTripleClass, weight_lower_inv]
      _ = weightLowerClass Cx := by rw [hrep]
      _ = weightLowerClass (Az * By) :=
        weight_lower_conj x (Az * By)
      _ =
          weightLowerClass Az +
            weightLowerClass By :=
        weight_lower_mul Az By
      _ =
          weightLowerClass A +
            weightLowerClass B := by
        rw [weight_lower_conj,
          weight_lower_conj]
      _ =
          weightTripleClass z⁻¹ x⁻¹ y +
            weightTripleClass y⁻¹ z x⁻¹ := by
        rfl
      _ =
          weightTripleClass z x y +
            weightTripleClass y z x := by
        simp
  calc
    weightTripleClass x y z +
          weightTripleClass y z x +
        weightTripleClass z x y =
        weightTripleClass x y z +
          (weightTripleClass z x y +
            weightTripleClass y z x) := by
      abel
    _ = weightTripleClass x y z +
          (-weightTripleClass x y z) := by
      rw [← hneg]
    _ = 0 := by simp

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr
open scoped commutatorElement

universe u

variable {α : Type u}

/-- Degree-three classes of left-normed triple commutators of free generators. -/
def generatorTripleSet :
    Set
      (Additive
        (LowerGradedLayer (FreeGroup α) 2)) :=
  {z | ∃ a b c : α,
    z = weightTripleClass
      (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c)}

/-- The integer span of degree-three triple commutators of free generators. -/
def generatorTripleSpan :
    Submodule ℤ
      (Additive
        (LowerGradedLayer (FreeGroup α) 2)) :=
  Submodule.span ℤ generatorTripleSet

/-- Every triple commutator of free generators belongs to the generator-triple span. -/
theorem triple_generator_span
    (a b c : α) :
    weightTripleClass
        (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c) ∈
      generatorTripleSpan (α := α) := by
  apply Submodule.subset_span
  exact ⟨a, b, c, rfl⟩

/--
By trilinearity modulo `γ₄`, every left-normed triple commutator class belongs
to the span of triple commutators of free generators.
-/
theorem three_triple_span
    (u v w : FreeGroup α) :
    weightTripleClass u v w ∈
      generatorTripleSpan (α := α) := by
  induction u using FreeGroup.induction_on with
  | C1 =>
      simp
  | of a =>
      induction v using FreeGroup.induction_on with
      | C1 =>
          simp
      | of b =>
          induction w using FreeGroup.induction_on with
          | C1 =>
              simp
          | of c =>
              exact triple_generator_span a b c
          | inv_of w hw =>
              simpa using
                (generatorTripleSpan (α := α)).neg_mem hw
          | mul w x hw hx =>
              simpa [three_triple_third] using
                (generatorTripleSpan (α := α)).add_mem hw hx
      | inv_of v hv =>
          simpa using
            (generatorTripleSpan (α := α)).neg_mem hv
      | mul v w hv hw =>
          simpa [three_triple_second] using
            (generatorTripleSpan (α := α)).add_mem hv hw
  | inv_of u hu =>
      simpa using
        (generatorTripleSpan (α := α)).neg_mem hu
  | mul u v hu hv =>
      simpa [three_triple_first] using
        (generatorTripleSpan (α := α)).add_mem hu hv

/--
Every degree-three bracket of an arbitrary `γ₂` element with an arbitrary
free-group word belongs to the generator-triple span.
-/
theorem bracket_triple_span
    (c : Subgroup.lowerCentralSeries (FreeGroup α) 1)
    (x : FreeGroup α) :
    weightBracketClass c x ∈
      generatorTripleSpan (α := α) := by
  have hc :
      (c : FreeGroup α) ∈
        Subgroup.closure (commutatorSet (FreeGroup α)) := by
    simpa [Subgroup.lowerCentralSeries_one, commutator_eq_closure] using c.property
  refine Subgroup.closure_induction
    (k := commutatorSet (FreeGroup α))
    (p := fun z hz =>
      weightBracketClass
          ⟨z, by
            rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
            exact hz⟩
          x ∈
        generatorTripleSpan (α := α))
    ?_ ?_ ?_ ?_ hc
  · intro z hz
    rw [commutatorSet_def] at hz
    rcases hz with ⟨u, v, rfl⟩
    exact three_triple_span u v x
  · change weightBracketClass
      (1 : Subgroup.lowerCentralSeries (FreeGroup α) 1) x ∈
        generatorTripleSpan (α := α)
    simp
  · intro z w hz hw hzm hwm
    rw [show
      (⟨z * w, by
          rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
          exact Subgroup.mul_mem _ hz hw⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 1) =
        (⟨z, by
          rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
          exact hz⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 1) *
        (⟨w, by
          rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
          exact hw⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 1) by
          rfl,
      three_bracket_left]
    exact (generatorTripleSpan (α := α)).add_mem hzm hwm
  · intro z hz hzm
    rw [show
      (⟨z⁻¹, by
          rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
          exact Subgroup.inv_mem _ hz⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 1) =
        (⟨z, by
          rw [Subgroup.lowerCentralSeries_one, commutator_eq_closure]
          exact hz⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 1)⁻¹ by
          rfl,
      bracket_class_inv]
    exact (generatorTripleSpan (α := α)).neg_mem hzm

/--
Every class represented by an element of `γ₃` belongs to the generator-triple
span.
-/
theorem generator_triple_span
    (g : Subgroup.lowerCentralSeries (FreeGroup α) 2) :
    weightLowerClass g ∈
      generatorTripleSpan (α := α) := by
  have hg :
      (g : FreeGroup α) ∈
        Subgroup.closure
          {z : FreeGroup α |
            ∃ c ∈ Subgroup.lowerCentralSeries (FreeGroup α) 1,
              ∃ x ∈ (⊤ : Subgroup (FreeGroup α)),
                c * x * c⁻¹ * x⁻¹ = z} := by
    simpa [Subgroup.lowerCentralSeries_succ] using g.property
  refine Subgroup.closure_induction
    (k :=
      {z : FreeGroup α |
        ∃ c ∈ Subgroup.lowerCentralSeries (FreeGroup α) 1,
          ∃ x ∈ (⊤ : Subgroup (FreeGroup α)),
            c * x * c⁻¹ * x⁻¹ = z})
    (p := fun z hz =>
      weightLowerClass
          ⟨z, by
            rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ]
            exact hz⟩ ∈
        generatorTripleSpan (α := α))
    ?_ ?_ ?_ ?_ hg
  · intro z hz
    rcases hz with ⟨c, hc, x, _hx, rfl⟩
    change weightBracketClass
      (⟨c, hc⟩ : Subgroup.lowerCentralSeries (FreeGroup α) 1) x ∈
        generatorTripleSpan (α := α)
    exact
      bracket_triple_span
        (⟨c, hc⟩ : Subgroup.lowerCentralSeries (FreeGroup α) 1) x
  · change weightLowerClass
      (1 : Subgroup.lowerCentralSeries (FreeGroup α) 2) ∈
        generatorTripleSpan (α := α)
    simp
  · intro z w hz hw hzm hwm
    simpa using
      (generatorTripleSpan (α := α)).add_mem hzm hwm
  · intro z hz hzm
    rw [show
      (⟨z⁻¹, by
          rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ]
          exact Subgroup.inv_mem _ hz⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 2) =
        (⟨z, by
          rw [show 2 = 1 + 1 by omega, Subgroup.lowerCentralSeries_succ]
          exact hz⟩ :
        Subgroup.lowerCentralSeries (FreeGroup α) 2)⁻¹ by
          rfl,
      weight_lower_inv]
    exact (generatorTripleSpan (α := α)).neg_mem hzm

/-- Generator triples span the full third lower-central associated-graded layer. -/
theorem triple_span_top :
    generatorTripleSpan (α := α) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective
      ((Subgroup.lowerCentralSeries (FreeGroup α) 3).subgroupOf
        (Subgroup.lowerCentralSeries (FreeGroup α) 2)) z.toMul
  change Additive.ofMul z.toMul ∈ generatorTripleSpan (α := α)
  rw [← hg]
  change weightLowerClass g ∈
    generatorTripleSpan (α := α)
  exact generator_triple_span g

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/-- The integer span of the canonical basic Hall classes in weight three. -/
def weightBasicSpan :
    Submodule ℤ
      (Additive
        (LowerGradedLayer (FreeGroup α) (3 - 1))) :=
  Submodule.span ℤ
    (Set.range fun i : BasicIndex (α := α) 3 =>
      (indexedBasicTree i).freeLowerWeight
        (n := 3) (indexed_tree_weight i))

/--
An admissible ordered generator triple is one of the canonical weight-three
basic Hall classes.
-/
theorem weight_triple_span
    (a b c : α)
    (hba : atom b < atom a)
    (hbc : atom b ≤ atom c) :
    weightTripleClass
        (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c) ∈
      weightBasicSpan (α := α) := by
  obtain ⟨i, hi⟩ :=
    indexed_basic_tree
      (basic_commutator_admissible
        (basic_commutator_admissible
          (isBasic_atom a) (isBasic_atom b) hba trivial)
        (isBasic_atom c)
        (lt_weight_lt (by simp))
        hbc)
      (show
        (commutator (commutator (atom a) (atom b)) (atom c)).weight = 3 by
          simp)
  apply Submodule.subset_span
  refine ⟨i, ?_⟩
  change
    (indexedBasicTree i).freeLowerWeight
        (indexed_tree_weight i) =
      weightTripleClass
        (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c)
  calc
    (indexedBasicTree i).freeLowerWeight
          (indexed_tree_weight i) =
        (commutator (commutator (atom a) (atom b)) (atom c)
          ).freeLowerWeight (by simp) :=
      free_lower_congr hi
        (indexed_tree_weight i) (by simp)
    _ =
        weightTripleClass
          (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c) := by
      rfl

/--
Once the inner generator pair is ordered, Jacobi repairs the only possible
weight-three Hall admissibility failure.
-/
theorem triple_basic_span
    (a b c : α)
    (hba : atom b < atom a) :
    weightTripleClass
        (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c) ∈
      weightBasicSpan (α := α) := by
  rcases le_or_gt (atom b) (atom c) with hbc | hcb
  · exact
      weight_triple_span
        a b c hba hbc
  · have hbcA :
        weightTripleClass
            (FreeGroup.of b) (FreeGroup.of c) (FreeGroup.of a) ∈
          weightBasicSpan (α := α) :=
      weight_triple_span
        b c a hcb (hcb.trans hba).le
    have hacB :
        weightTripleClass
            (FreeGroup.of a) (FreeGroup.of c) (FreeGroup.of b) ∈
          weightBasicSpan (α := α) :=
      weight_triple_span
        a c b (hcb.trans hba) hcb.le
    have hjacobi :=
      weight_triple_jacobi
        (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c)
    have heq :
        weightTripleClass
            (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c) =
          -weightTripleClass
              (FreeGroup.of b) (FreeGroup.of c) (FreeGroup.of a) +
            weightTripleClass
              (FreeGroup.of a) (FreeGroup.of c) (FreeGroup.of b) := by
      rw [swap_first_second
        (FreeGroup.of c) (FreeGroup.of a) (FreeGroup.of b)]
      calc
        weightTripleClass
              (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c) =
            (weightTripleClass
                  (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c) +
                weightTripleClass
                  (FreeGroup.of b) (FreeGroup.of c) (FreeGroup.of a) +
                weightTripleClass
                  (FreeGroup.of c) (FreeGroup.of a) (FreeGroup.of b)) +
              (-weightTripleClass
                  (FreeGroup.of b) (FreeGroup.of c) (FreeGroup.of a) +
                -weightTripleClass
                  (FreeGroup.of c) (FreeGroup.of a) (FreeGroup.of b)) := by
            abel
        _ =
            -weightTripleClass
                (FreeGroup.of b) (FreeGroup.of c) (FreeGroup.of a) +
              -weightTripleClass
                (FreeGroup.of c) (FreeGroup.of a) (FreeGroup.of b) := by
          rw [hjacobi, zero_add]
    rw [heq]
    exact (weightBasicSpan (α := α)).add_mem
      ((weightBasicSpan (α := α)).neg_mem hbcA)
      hacB

/-- Every generator triple class belongs to the canonical weight-three Hall span. -/
theorem triple_class_span
    (a b c : α) :
    weightTripleClass
        (FreeGroup.of a) (FreeGroup.of b) (FreeGroup.of c) ∈
      weightBasicSpan (α := α) := by
  rcases lt_trichotomy (atom b) (atom a) with hba | hba | hab
  · exact triple_basic_span a b c hba
  · cases hba
    simp
  · rw [swap_first_second]
    exact
      (weightBasicSpan (α := α)).neg_mem
        (triple_basic_span b a c hab)

/-- The canonical weight-three Hall classes span the full degree-three layer. -/
theorem indexed_tree_top :
    Submodule.span ℤ
        (Set.range fun i : BasicIndex (α := α) 3 =>
          (indexedBasicTree i).freeLowerWeight
            (n := 3) (indexed_tree_weight i)) =
      ⊤ := by
  apply top_unique
  rw [← triple_span_top]
  apply Submodule.span_le.2
  intro z hz
  rcases hz with ⟨a, b, c, rfl⟩
  exact triple_class_span a b c

/-- The weight-three Hall classes form a basis of the free-group graded layer. -/
def freeBasisInput :
    FBInput (α := α) 3 where
  pivots := signedStandardPivots ℤ
  span_eq_top :=
    indexed_tree_top

end HallTree
end Submission


noncomputable section

namespace Submission
namespace HallTree

universe u

variable {α : Type u} [Fintype α] [DecidableEq α] [Encodable α]

/--
The free-group lower-central Hall basis input is formalized uniformly in
every positive weight through three.
-/
def freeInputPos
    {r : ℕ}
    (hrPos : 0 < r)
    (hr : r ≤ 3) :
    FBInput (α := α) r := by
  interval_cases r
  · exact weightBasisInput
  · exact lowerBasisInput
  · exact freeBasisInput

end HallTree
end Submission
