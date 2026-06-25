import Submission.Group.Zassenhaus.Constructors

/-!
# Scaled atomic sources for symbolic Hall powers

Compressing `q` identical raw Hall coordinates produces coordinatewise-scaled
atomic factors.  In a noncommutative truncation this need not be the `q`th
power of the whole collected Hall block.  This file proves the exact
coordinatewise-scaled evaluation theorem, constructs a reflexive symbolic run
when the two values agree, and supplies that agreement automa for a
commutative truncation.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped IsMulCommutative

/--
In a commutative group, scaling every exponent in a finite ordered product by
`q` gives the `q`th power of the original product.
-/
lemma zpow_nat_cast
    {G α : Type*}
    [Group G]
    [IsMulCommutative G]
    (g : α → G)
    (e : α → ℤ)
    (L : List α)
    (q : ℕ) :
    (L.map fun i => g i ^ (e i * (q : ℤ))).prod =
      (L.map fun i => g i ^ e i).prod ^ q := by
  induction L with
  | nil =>
      simp
  | cons i L ih =>
      simp only [List.map_cons, List.prod_cons]
      have hi :
          g i ^ (e i * (q : ℤ)) = (g i ^ e i) ^ q := by
        rw [← zpow_natCast, ← zpow_mul]
      calc
        g i ^ (e i * (q : ℤ)) *
              (L.map fun j => g j ^ (e j * (q : ℤ))).prod =
            (g i ^ e i) ^ q * (L.map fun j => g j ^ e j).prod ^ q := by
              rw [ih, hi]
        _ = (g i ^ e i * (L.map fun j => g j ^ e j).prod) ^ q := by
              rw [mul_pow]

/-- Coordinatewise exponent scaling distributes over one Hall-weight layer. -/
lemma BCWta.collec_produ_halle
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    [IsMulCommutative
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)]
    (e : HEFam H)
    (q s : ℕ) :
    (H s).collectedWeightProduct (n := n) (scaledExponentFamily e q s) =
      (H s).collectedWeightProduct (n := n) (e s) ^ q := by
  simp only [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    BCWt.evalin_freelower_centtrunterm,
    scaledExponentFamily]
  exact congrArg Subtype.val
    (zpow_nat_cast
      (fun i =>
        ((H s).commutator i).evalin_freelower_centtrunterm (n := n))
      (e s) (Finset.univ.sort fun i i' : (H s).index => i ≤ i') q)

/-- Coordinatewise exponent scaling distributes over every collected Hall prefix. -/
lemma collected_scaled_family
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    [IsMulCommutative
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)]
    (e : HEFam H)
    (q k : ℕ) :
    collectedPrefixProduct (n := n) H (scaledExponentFamily e q) k =
      collectedPrefixProduct (n := n) H e k ^ q := by
  induction k with
  | zero =>
      simp [collectedPrefixProduct]
  | succ k ih =>
      rw [collected_prefix_succ, collected_prefix_succ,
        ih, BCWta.collec_produ_halle]
      rw [mul_pow]

/-- In a commutative truncation, coordinatewise scaling is the whole-block power. -/
lemma collected_scaled_exponent
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    [IsMulCommutative
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)]
    (e : HEFam H)
    (q : ℕ) :
    collectedHallProduct (n := n) H (scaledExponentFamily e q) =
      collectedHallProduct (n := n) H e ^ q := by
  exact collected_scaled_family e q (n - 1)

/-- The lower-central truncation at cutoff two is the abelianization. -/
instance inst_commutative_truncation
    (Q : Type u)
    [Group Q] :
    IsMulCommutative (LowerCentralTruncation Q 2) := by
  dsimp [LowerCentralTruncation]
  exact
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      (by
        simpa only [Nat.reduceSubDiff, Subgroup.lowerCentralSeries_one] using
          (le_rfl : _root_.commutator Q ≤ _root_.commutator Q))

/-- The normalized atomic endpoint obtained from coordinatewise scaling. -/
noncomputable def scaledCoordinateExpansions
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    CCExpans H inputWeight where
  expansion := scaledCoordinateExpansion e

/-- Evaluating the normalized atomic endpoint gives coordinatewise scaling. -/
lemma scaled_coordinate_expansions
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (q : ℕ) :
    (scaledCoordinateExpansions
      (inputWeight := inputWeight) e).eval q =
        scaledExponentFamily e q := by
  funext s i
  exact congrFun (scaled_coordinate_expansion e heBelow s i) q

namespace TCRun

/--
If coordinatewise scaling equals the power of the whole collected block, its
normalized atomic endpoint is already a complete reflexive symbolic run.
-/
noncomputable def scaled_hall_coordinates
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (hscaled :
      ∀ q : ℕ,
        collectedHallProduct (n := n) H (scaledExponentFamily e q) =
          collectedHallProduct (n := n) H e ^ q) :
    TCRun (n := n)
      (inputWeight := inputWeight) H e := by
  let R : CCExpans H inputWeight :=
    scaledCoordinateExpansions e
  exact
    { source := R.factors (n := n)
      coordinates := R
      source_isTruncated := R.isTruncated_factors
      list_eval_source := fun q => by
        calc
          SPFactora.listEval (n := n) q (R.factors (n := n)) =
              collectedHallProduct (n := n) H (R.eval q) :=
            R.listEval_factors q
          _ = collectedHallProduct (n := n) H (scaledExponentFamily e q) := by
            rw [scaled_coordinate_expansions e heBelow q]
          _ = collectedHallProduct (n := n) H e ^ q :=
            hscaled q
      rewrites := Relation.ReflTransGen.refl }

/--
In a commutative truncation, the normalized scaled atomic endpoint is
automa a complete symbolic repeated-power run.
-/
noncomputable def mul_commutative
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    [IsMulCommutative
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)]
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    TCRun (n := n)
      (inputWeight := inputWeight) H e :=
  scaled_hall_coordinates e heBelow
    (collected_scaled_exponent e)

/--
At cutoff two, the abelianized free group has a complete scaled-coordinate
symbolic repeated-power run.
-/
noncomputable def of_cutoff_two
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    TCRun (n := 2)
      (inputWeight := inputWeight) H e :=
  mul_commutative e heBelow

end TCRun

/-- Claim 5 explicit expansion data is fully constructed at cutoff two. -/
theorem collected_expansion_two
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    CEData (n := 2) H e inputWeight :=
  (TCRun.of_cutoff_two e heBelow).coordinateExpansionData

/-- Claim 5 polynomial data is fully constructed at cutoff two. -/
theorem collected_data_two
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    CollectedPolynomialData (n := 2) H e inputWeight :=
  (TCRun.of_cutoff_two e heBelow).coordinatePolynomialData
    hinputWeight

end TCTex
end Submission
