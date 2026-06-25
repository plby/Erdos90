import Submission.Group.Petresco.CertifiedFactors

/-!
# Provenance-preserving Hall collection

This file records the semantic endpoint of an Edmonton collection.  The
collector may retain an arbitrary free-group conjugator on every output
factor; exact bidegree and signed-binomial provenance live in
`CFactor`.
-/

namespace Submission
namespace Edmonton

universe u

/-- Evaluate an ordered list of certified factors. -/
def certifiedFactorEval
    {G : Type u} [Group G] {M N : ℕ}
    (x y : G) (factors : List (CFactor M N)) : G :=
  (factors.map (CFactor.eval x y)).prod

@[simp]
lemma certified_factor_nil
    {G : Type u} [Group G] {M N : ℕ} (x y : G) :
    certifiedFactorEval x y ([] : List (CFactor M N)) = 1 :=
  rfl

@[simp]
lemma certified_factor_cons
    {G : Type u} [Group G] {M N : ℕ}
    (x y : G) (factor : CFactor M N)
    (factors : List (CFactor M N)) :
    certifiedFactorEval x y (factor :: factors) =
      factor.eval x y * certifiedFactorEval x y factors :=
  rfl

/-- Every ordered product of certified factors lies in the admissible Hall
subgroup. -/
lemma certified_factor_admissible
    {G : Type u} [Group G] {M N : ℕ} {x y : G} :
    ∀ factors : List (CFactor M N),
      certifiedFactorEval x y factors ∈
        admissibleHallSubgroup M N x y
  | [] =>
      (admissibleHallSubgroup M N x y).one_mem
  | factor :: factors =>
      (admissibleHallSubgroup M N x y).mul_mem
        factor.eval_memadmissible_hallsubgroup
        (certified_factor_admissible factors)

/-- A complete provenance-preserving collection of the four signed input
blocks `x⁻ᴹ, y⁻ᴺ, xᴹ, yᴺ`. -/
structure AHColl (M N : ℕ) where
  factors : List (CFactor M N)
  eval_eq :
    ∀ {G : Type u} [Group G] (x y : G),
      certifiedFactorEval x y factors =
        hallCommutator (x ^ M) (y ^ N)

namespace AHColl

/-- The normal-closure theorem is the direct semantic consumer of a certified
collection. -/
lemma powers_admissible_subgroup
    {M N : ℕ}
    (collection : AHColl.{u} M N)
    {G : Type u} [Group G] (x y : G) :
    hallCommutator (x ^ M) (y ^ N) ∈
      admissibleHallSubgroup M N x y := by
  rw [← collection.eval_eq x y]
  exact certified_factor_admissible collection.factors

/-- A zero left block has the empty certified collection. -/
def zero_left (N : ℕ) :
    AHColl.{u} 0 N where
  factors := []
  eval_eq := by
    intro G _inst x y
    simp [hallCommutator]

/-- A zero right block has the empty certified collection. -/
def zero_right (M : ℕ) :
    AHColl.{u} M 0 where
  factors := []
  eval_eq := by
    intro G _inst x y
    simp [hallCommutator]

/-- The basic formal bracket as a certified `(1,1)` factor. -/
def basicFactor :
    CFactor 1 1 where
  word := formalBracket (FreeMagma.of false) (FreeMagma.of true)
  exponent := 1
  conjugator := 1
  mixed := by
    simp [leftDegree, rightDegree, formalBidegree, formalGrade,
      formalBracket]
  admissible := by
    apply Submodule.subset_span
    refine
      ⟨[{ sign := .positive, degree := 1 }],
        [{ sign := .positive, degree := 1 }], ?_, ?_, ?_⟩
    all_goals
      simp [admissibleBlockDegree, admissibleBlockProduct, signedChoose,
        leftDegree, rightDegree, formalBidegree, formalGrade, formalBracket]

/-- The base commutator is already one certified factor. -/
def one_one :
    AHColl.{u} 1 1 where
  factors := [basicFactor]
  eval_eq := by
    intro G _inst x y
    simp [basicFactor, CFactor.eval, certifiedFactorEval]

end AHColl

end Edmonton
end Submission
