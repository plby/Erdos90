import Submission.CantEick.PetrescoCoordinatePolynomial
import Submission.Group.Edmonton.HallEmbeddings

/-!
# Bridge from Hall canonical bases to Cant--Eick product variables

Hall's Theorem 6.5 is proved in `HallEmbeddingTheorems` using the
`BExpr` syntax.  This file reindexes its multiplication and power
coordinate expressions into the `left`/`right` product-variable convention used
by the Cant--Eick coordinate-polynomial interface.
-/

namespace Submission
namespace CantEick

universe u

open Edmonton

namespace PVariaba

/-- Convert the `Sum`-indexed multiplication variables used by
`HallEmbeddingTheorems` into Cant--Eick product variables. -/
def ofSum {ι : Type u} : Sum ι ι → PVariaba ι
  | Sum.inl i => PVariaba.left i
  | Sum.inr i => PVariaba.right i

@[simp]
theorem assignment_sum_inl {ι : Type u} (a b : ι → ℤ) (i : ι) :
    PVariaba.assignment a b (ofSum (Sum.inl i)) = a i :=
  rfl

@[simp]
theorem assignment_sum_inr {ι : Type u} (a b : ι → ℤ) (i : ι) :
    PVariaba.assignment a b (ofSum (Sum.inr i)) = b i :=
  rfl

@[simp]
theorem assignment_comp_sum {ι : Type u} (a b : ι → ℤ) :
    (fun s : Sum ι ι => PVariaba.assignment a b (ofSum s)) =
      Sum.elim a b := by
  funext s
  cases s <;> rfl

end PVariaba

/-- Variables for a Hall power-coordinate polynomial: the distinguished
exponent variable and the coordinate variables of the base element. -/
inductive PVariab (ι : Type u) : Type u where
  | exponent : PVariab ι
  | coord : ι → PVariab ι

namespace PVariab

/-- The integer assignment associated to an exponent and a Hall-coordinate
vector. -/
def assignment {ι : Type u} (m : ℤ) (a : ι → ℤ) : PVariab ι → ℤ
  | PVariab.exponent => m
  | PVariab.coord i => a i

/-- Convert the `Option`-indexed power variables used by
`HallEmbeddingTheorems` into Cant--Eick power variables. -/
def ofOption {ι : Type u} : Option ι → PVariab ι
  | none => PVariab.exponent
  | some i => PVariab.coord i

@[simp]
theorem assignment_option_none {ι : Type u} (m : ℤ) (a : ι → ℤ) :
    assignment m a (ofOption (none : Option ι)) = m :=
  rfl

@[simp]
theorem assignment_option_some {ι : Type u} (m : ℤ) (a : ι → ℤ) (i : ι) :
    assignment m a (ofOption (some i)) = a i :=
  rfl

@[simp]
theorem assignment_comp_option {ι : Type u} (m : ℤ) (a : ι → ℤ) :
    (fun s : Option ι => assignment m a (ofOption s)) =
      canonicalPowAssignment m a := by
  funext s
  cases s <;> rfl

end PVariab

variable {G : Type u} [Group G]

/-- Cant--Eick's recursive integer binomial coefficient agrees with
Mathlib's binomial-ring coefficient on `ℤ`. -/
theorem int_binom_choose (z : ℤ) :
    ∀ k : ℕ, intBinom z k = Ring.choose z k
  | 0 => by
      simp [intBinom]
  | k + 1 => by
      rw [intBinom, int_binom_choose z k]
      symm
      apply Int.eq_ediv_of_mul_eq_right
      · change ((k + 1 : ℕ) : ℤ) ≠ 0
        exact_mod_cast Nat.succ_ne_zero k
      · have h :=
          Ring.choose_smul_choose (R := ℤ) z
            (n := k + 1) (k := k) (Nat.le_succ k)
        simpa [nsmul_eq_mul, Nat.choose_succ_self_right,
          Ring.choose_one_right, Nat.cast_add, Nat.cast_one,
          mul_comm, mul_left_comm, mul_assoc] using h

namespace IVPoly

/-- Translate Hall's compositional `BExpr` syntax into the
Cant--Eick integer-valued polynomial syntax. -/
def ofBinomialExpression {σ : Type u} :
    BExpr σ → IVPoly σ
  | .const z => .const z
  | .var i => .var i
  | .add p q => .add (ofBinomialExpression p) (ofBinomialExpression q)
  | .mul p q => .mul (ofBinomialExpression p) (ofBinomialExpression q)
  | .choose p k => .binom (ofBinomialExpression p) k

/--
Evaluation of the translation agrees with Hall's `BExpr`
evaluation.
-/
theorem eval_binomial_expression {σ : Type u}
    (x : σ → ℤ) :
    ∀ p : BExpr σ,
      IVPoly.eval x (ofBinomialExpression p) =
        BExpr.eval x p
  | .const _ => rfl
  | .var _ => rfl
  | .add p q => by
      simp only [ofBinomialExpression, IVPoly.eval,
        BExpr.eval,
        eval_binomial_expression x p,
        eval_binomial_expression x q]
  | .mul p q => by
      simp only [ofBinomialExpression, IVPoly.eval,
        BExpr.eval,
        eval_binomial_expression x p,
        eval_binomial_expression x q]
  | .choose p k => by
      simp only [ofBinomialExpression, IVPoly.eval,
        BExpr.eval,
        eval_binomial_expression x p, int_binom_choose]

end IVPoly

/--
Hall's Theorem 6.5, in Cant--Eick product-variable form: in any Hall
canonical basis, every product coordinate is represented by a universal
compositional binomial expression in the left and right coordinates.
-/
theorem coordinate_binomial_expressions {M : ℕ}
    (b : Edmonton.HCBasis G M) :
    ∃ P : Fin M → BExpr (PVariaba (Fin M)),
      ∀ (a c : Fin M → ℤ) (i : Fin M),
        BExpr.eval (PVariaba.assignment a c) (P i) =
          b.coord (b.coord.symm a * b.coord.symm c) i := by
  refine
    ⟨fun i =>
      BExpr.rename PVariaba.ofSum (b.mulExpression i),
      ?_⟩
  intro a c i
  rw [BExpr.eval_rename]
  rw [PVariaba.assignment_comp_sum]
  simpa [canonicalMulCoordinate] using
    b.eval_expression_int i (Sum.elim a c)

/--
Power-coordinate analogue of the preceding bridge: every integer-power
coordinate is represented by a universal compositional binomial expression in
the exponent and base coordinates.
-/
theorem canonical_binomial_expressions {M : ℕ}
    (b : Edmonton.HCBasis G M) :
    ∃ K : Fin M → BExpr (PVariab (Fin M)),
      ∀ (a : Fin M → ℤ) (m : ℤ) (i : Fin M),
        BExpr.eval (PVariab.assignment m a) (K i) =
          b.coord ((b.coord.symm a) ^ m) i := by
  refine
    ⟨fun i =>
      BExpr.rename PVariab.ofOption (b.powExpression i),
      ?_⟩
  intro a m i
  rw [BExpr.eval_rename]
  rw [PVariab.assignment_comp_option]
  simpa [canonicalPowCoordinate] using
    b.pow_expression_int i (canonicalPowAssignment m a)

/--
Combined Hall-Petresco coordinate package from Hall's Theorem 6.5 for an
abstract Hall canonical basis.  This is the expression-valued source that a
future concrete free-nilpotent bridge can transport into the collection-bound
polynomial data.
-/
theorem basis_binomial_expressions {M : ℕ}
    (b : Edmonton.HCBasis G M) :
    (∃ P : Fin M → BExpr (PVariaba (Fin M)),
      ∀ (a c : Fin M → ℤ) (i : Fin M),
        BExpr.eval (PVariaba.assignment a c) (P i) =
          b.coord (b.coord.symm a * b.coord.symm c) i) ∧
    (∃ K : Fin M → BExpr (PVariab (Fin M)),
      ∀ (a : Fin M → ℤ) (m : ℤ) (i : Fin M),
        BExpr.eval (PVariab.assignment m a) (K i) =
          b.coord ((b.coord.symm a) ^ m) i) :=
  ⟨coordinate_binomial_expressions b,
    canonical_binomial_expressions b⟩

/--
Hall's product-coordinate theorem in Cant--Eick's `IVPoly`
syntax, conditional only on identifying the two integer binomial coefficient
implementations.
-/
theorem basis_valued_polynomials
    {M : ℕ}
    (b : Edmonton.HCBasis G M) :
    ∃ P : Fin M → IVPoly (PVariaba (Fin M)),
      ∀ (a c : Fin M → ℤ) (i : Fin M),
        IVPoly.eval (PVariaba.assignment a c) (P i) =
          b.coord (b.coord.symm a * b.coord.symm c) i := by
  obtain ⟨P, hP⟩ :=
    coordinate_binomial_expressions b
  refine
    ⟨fun i => IVPoly.ofBinomialExpression (P i), ?_⟩
  intro a c i
  rw [IVPoly.eval_binomial_expression]
  exact hP a c i

/--
Hall's power-coordinate theorem in Cant--Eick's `IVPoly` syntax.
-/
theorem canonical_valued_polynomials
    {M : ℕ}
    (b : Edmonton.HCBasis G M) :
    ∃ K : Fin M → IVPoly (PVariab (Fin M)),
      ∀ (a : Fin M → ℤ) (m : ℤ) (i : Fin M),
        IVPoly.eval (PVariab.assignment m a) (K i) =
          b.coord ((b.coord.symm a) ^ m) i := by
  obtain ⟨K, hK⟩ :=
    canonical_binomial_expressions b
  refine
    ⟨fun i => IVPoly.ofBinomialExpression (K i), ?_⟩
  intro a m i
  rw [IVPoly.eval_binomial_expression]
  exact hK a m i

/--
Combined `IVPoly` form of Hall's Theorem 6.5 for an abstract
Hall canonical basis.
-/
theorem int_valued_polynomials
    {M : ℕ}
    (b : Edmonton.HCBasis G M) :
    (∃ P : Fin M → IVPoly (PVariaba (Fin M)),
      ∀ (a c : Fin M → ℤ) (i : Fin M),
        IVPoly.eval (PVariaba.assignment a c) (P i) =
          b.coord (b.coord.symm a * b.coord.symm c) i) ∧
    (∃ K : Fin M → IVPoly (PVariab (Fin M)),
      ∀ (a : Fin M → ℤ) (m : ℤ) (i : Fin M),
        IVPoly.eval (PVariab.assignment m a) (K i) =
          b.coord ((b.coord.symm a) ^ m) i) :=
  ⟨basis_valued_polynomials
      b,
    canonical_valued_polynomials
      b⟩

/--
Package Hall's product-coordinate polynomials for an abstract Hall canonical
basis as a Cant--Eick coordinate model, once the selected product polynomials
are known to be triangular for the supplied weight function.
-/
noncomputable def modelCanonicalBasis
    {M d n : ℕ}
    (b : Edmonton.HCBasis G M)
    (weight : Fin M → ℕ)
    (hweight : ∀ i : Fin M, weight i < n)
    (htri :
      ∀ i : Fin M,
        ∃ Q : IVPoly (PVariaba (Fin M)),
          Classical.choose
                (basis_valued_polynomials
                  b) i =
              IVPoly.X (PVariaba.left i) +
              IVPoly.X (PVariaba.right i) +
              Q ∧
            DependsOnlyBelow (PVariaba.weight weight) (weight i) Q) :
    HCModel d n M where
  N := G
  mul := fun x y => x * y
  basis := b.generators
  weight := weight
  weight_lt_nilpotency := hweight
  normalForm := b.coord.symm
  coord := b.coord
  coord_normalForm := by
    intro a
    exact b.coord.apply_symm_apply a
  normalForm_coord := by
    intro g
    exact b.coord.symm_apply_apply g
  prodPoly :=
    Classical.choose
      (basis_valued_polynomials b)
  prodPoly_eval := by
    intro a c i
    exact
      (Classical.choose_spec
          (basis_valued_polynomials
            b) a c i).symm
  prodPoly_triangular := htri

/--
Cant--Eick's triangular product-law statement follows from Hall's canonical
basis theorem together with the remaining triangularity/support assertion for
the chosen product-coordinate polynomials.
-/
theorem triangular_gh_ce
    {M d n : ℕ}
    (b : Edmonton.HCBasis G M)
    (weight : Fin M → ℕ)
    (hweight : ∀ i : Fin M, weight i < n)
    (htri :
      ∀ i : Fin M,
        ∃ Q : IVPoly (PVariaba (Fin M)),
          Classical.choose
                (basis_valued_polynomials
                  b) i =
              IVPoly.X (PVariaba.left i) +
              IVPoly.X (PVariaba.right i) +
              Q ∧
            DependsOnlyBelow (PVariaba.weight weight) (weight i) Q) :
    ∃ P : Fin M → IVPoly (PVariaba (Fin M)),
      (∀ a c : Fin M → ℤ,
        (b.coord.symm a * b.coord.symm c) =
          b.coord.symm
            (fun i =>
              IVPoly.eval
                (PVariaba.assignment a c) (P i))) ∧
      (∀ i : Fin M, ∃ Q : IVPoly (PVariaba (Fin M)),
        P i =
            IVPoly.X (PVariaba.left i) +
            IVPoly.X (PVariaba.right i) +
            Q ∧
          DependsOnlyBelow (PVariaba.weight weight) (weight i) Q) :=
  triangularGHCE
    (modelCanonicalBasis
      (d := d) (n := n) b weight hweight htri)

end CantEick
end Submission
