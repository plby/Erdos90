import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.FinCases
import Towers.NumberTheory.Density.QuarticChebotarevDensities

/-!
# Milne, Chapter 8, Example 8.37: the dihedral quartic density table

The dihedral group of the square has order eight.  In its action on the four
vertices, its elements have cycle-type counts

* one identity;
* two transpositions;
* three double transpositions;
* two four-cycles.

The double transpositions occupy two conjugacy classes, of sizes one and two.
Using additivity of natural density for their disjoint union, Chebotarev gives
Milne's densities `1/8`, `1/4`, `3/8`, and `1/4`.
-/

namespace Towers.NumberTheory.Milne

open DihedralGroup IsDedekindDomain NumberField

noncomputable section

private abbrev SquareDihedralGroup := DihedralGroup 4

/-- The faithful action of the dihedral group on the vertices `ZMod 4` of a
square.  Rotations act by subtraction and reflections by `x ↦ i - x`; this
choice matches Mathlib's multiplication convention for `DihedralGroup`. -/
def squareDihedralAction : SquareDihedralGroup →* Equiv.Perm (ZMod 4) where
  toFun
    | r i => Equiv.addRight (-i)
    | sr i => Equiv.subLeft i
  map_one' := by
    change Equiv.addRight (-(0 : ZMod 4)) = 1
    ext x
    simp
  map_mul' a b := by
    cases a with
    | r i =>
      cases b with
      | r j => ext x ; simp
      | sr j => ext x ; simp ; ring
    | sr i =>
      cases b with
      | r j => ext x ; simp ; ring
      | sr j => ext x ; simp ; ring

/-- The two nontrivial rotations are four-cycles. -/
theorem dihedral_rotation_types :
    (squareDihedralAction (r 1)).cycleType = {4} ∧
      (squareDihedralAction (r 3)).cycleType = {4} := by
  decide

/-- The half-turn and the odd reflections are double transpositions. -/
theorem double_transposition_types :
    (squareDihedralAction (r 2)).cycleType = {2, 2} ∧
      (squareDihedralAction (sr 1)).cycleType = {2, 2} ∧
      (squareDihedralAction (sr 3)).cycleType = {2, 2} := by
  decide

/-- The even reflections are transpositions fixing the other two vertices. -/
theorem dihedral_transposition_types :
    (squareDihedralAction (sr 0)).cycleType = {2} ∧
      (squareDihedralAction (sr 2)).cycleType = {2} := by
  decide

private theorem square_dihedral_conjugacy
    (g x : SquareDihedralGroup) :
    x ∈ (ConjClasses.mk g).carrier ↔ IsConj x g := by
  rw [ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj]

private theorem dihedral_r_carrier :
    (ConjClasses.mk (r 1 : SquareDihedralGroup)).carrier = {r 1, r 3} := by
  ext x
  rw [square_dihedral_conjugacy]
  cases x with
  | r i => fin_cases i <;> decide
  | sr i => fin_cases i <;> decide

private theorem square_r_carrier :
    (ConjClasses.mk (r 2 : SquareDihedralGroup)).carrier = {r 2} := by
  ext x
  rw [square_dihedral_conjugacy]
  cases x with
  | r i => fin_cases i <;> decide
  | sr i => fin_cases i <;> decide

private theorem dihedral_sr_carrier :
    (ConjClasses.mk (sr 0 : SquareDihedralGroup)).carrier = {sr 0, sr 2} := by
  ext x
  rw [square_dihedral_conjugacy]
  cases x with
  | r i => fin_cases i <;> decide
  | sr i => fin_cases i <;> decide

private theorem square_sr_carrier :
    (ConjClasses.mk (sr 1 : SquareDihedralGroup)).carrier = {sr 1, sr 3} := by
  ext x
  rw [square_dihedral_conjugacy]
  cases x with
  | r i => fin_cases i <;> decide
  | sr i => fin_cases i <;> decide

@[simp]
theorem dihedral_r_ncard :
    (ConjClasses.mk (r 1 : SquareDihedralGroup)).carrier.ncard = 2 := by
  rw [dihedral_r_carrier]
  exact Set.ncard_pair (by decide)

@[simp]
theorem r_conjugacy_ncard :
    (ConjClasses.mk (r 2 : SquareDihedralGroup)).carrier.ncard = 1 := by
  rw [square_r_carrier]
  simp

@[simp]
theorem dihedral_sr_ncard :
    (ConjClasses.mk (sr 0 : SquareDihedralGroup)).carrier.ncard = 2 := by
  rw [dihedral_sr_carrier]
  exact Set.ncard_pair (by decide)

@[simp]
theorem sr_conjugacy_ncard :
    (ConjClasses.mk (sr 1 : SquareDihedralGroup)).carrier.ncard = 2 := by
  rw [square_sr_carrier]
  exact Set.ncard_pair (by decide)

private theorem square_dihedral_card : Nat.card SquareDihedralGroup = 8 := by
  simpa using DihedralGroup.nat_card (n := 4)

variable (K : Type*) [Field K] [NumberField K]

/-- Complete splitting has density `1/8` for a dihedral quartic extension. -/
theorem dihedral_density_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses SquareDihedralGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk 1))
      (1 / 8) := by
  simpa [square_dihedral_card] using
    (identity_frobenius_density K hcheb)

/-- The transposition factorization type has density `1/4`. -/
theorem dihedral_transposition_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses SquareDihedralGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk (sr 0)))
      (1 / 4) := by
  have h := hcheb (ConjClasses.mk (sr 0))
  rw [dihedral_sr_ncard,
    square_dihedral_card] at h
  convert h using 1 ; norm_num

/-- The two double-transposition conjugacy classes together have density
`3/8`. -/
theorem dihedral_double_transposition
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses SquareDihedralGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk (r 2)) ∪
        primesFrobeniusClass K frobeniusClass (ConjClasses.mk (sr 1)))
      (3 / 8) := by
  have hne :
      ConjClasses.mk (r 2 : SquareDihedralGroup) ≠ ConjClasses.mk (sr 1) := by
    intro h
    rw [ConjClasses.mk_eq_mk_iff_isConj] at h
    exact (by decide : ¬IsConj (r 2 : SquareDihedralGroup) (sr 1)) h
  have hdisjoint :
      Disjoint
        (primesFrobeniusClass K frobeniusClass (ConjClasses.mk (r 2)))
        (primesFrobeniusClass K frobeniusClass (ConjClasses.mk (sr 1))) := by
    rw [Set.disjoint_left]
    intro p hp hq
    exact hne (Option.some.inj (hp.symm.trans hq))
  have hrotation := hcheb (ConjClasses.mk (r 2))
  have hreflection := hcheb (ConjClasses.mk (sr 1))
  rw [r_conjugacy_ncard,
    square_dihedral_card] at hrotation
  rw [sr_conjugacy_ncard,
    square_dihedral_card] at hreflection
  have hunion := PNDensit.union_of_disjoint K
    hrotation hreflection hdisjoint
  convert hunion using 1 ; norm_num

/-- The irreducible four-cycle factorization type has density `1/4`. -/
theorem dihedral_quartic_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses SquareDihedralGroup)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk (r 1)))
      (1 / 4) := by
  have h := hcheb (ConjClasses.mk (r 1))
  rw [dihedral_r_ncard,
    square_dihedral_card] at h
  convert h using 1 ; norm_num

end


end Towers.NumberTheory.Milne
