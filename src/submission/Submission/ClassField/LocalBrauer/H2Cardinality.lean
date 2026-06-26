import Submission.ClassField.CrossedProducts.Multiplicative2Comparison
import Submission.ClassField.CrossedProducts.Cohomology
import Submission.ClassField.LocalBrauer.LocalInvariantTorsion

/-!
# Cardinality of finite local degree-two cohomology

Given local invariant equivalences for the base and extension fields and the
base-change formula between them, the relative Brauer group of a finite
Galois extension is the subgroup of `Q/Z` killed by the extension degree.
Theorem IV.3.14 and the comparison of the two presentations of `H²` then
give the cardinality hypothesis used in Tate's theorem.
-/

namespace Submission.CField.LBrauer

noncomputable section

open BGroups CProduca

variable (K L : Type)
  [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The multiplicative form of the subgroup of `ℚ/ℤ` killed by `n`. -/
def invariantPowTorsion (n : ℕ) :
    Subgroup (Multiplicative LocalInvariant) where
  carrier := {x | x ^ n = 1}
  one_mem' := one_pow n
  mul_mem' := by
    intro x y hx hy
    change (x * y) ^ n = 1
    change x ^ n = 1 at hx
    change y ^ n = 1 at hy
    rw [mul_pow, hx, hy, one_mul]
  inv_mem' := by
    intro x hx
    change x⁻¹ ^ n = 1
    change x ^ n = 1 at hx
    rw [inv_pow, hx, inv_one]

/-- Additive and multiplicative descriptions of finite local-invariant
torsion agree. -/
noncomputable def invariantTorsionPow (n : ℕ) :
    Multiplicative (localInvariantTorsion n) ≃*
      invariantPowTorsion n where
  toFun x := ⟨Multiplicative.ofAdd (x.toAdd : LocalInvariant), by
    change n • ((x.toAdd : localInvariantTorsion n) : LocalInvariant) = 0
    exact x.toAdd.property⟩
  invFun x := Multiplicative.ofAdd ⟨x.1.toAdd, by
    change x.1 ^ n = 1
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Under the base-change formula, the relative Brauer group is exactly the
degree-torsion subgroup of the local invariant group. -/
noncomputable def relativeBrauerTorsion
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L) :
    relativeBrauerGroup K L ≃*
      invariantPowTorsion (Module.finrank K L) where
  toFun x := ⟨invK (x : BrauerGroup K), by
    change (invK (x : BrauerGroup K)) ^
      Module.finrank K L = 1
    rw [← hbase, x.property, map_one]⟩
  invFun y := ⟨invK.symm y.1, by
    rw [relative_brauer_group]
    apply invL.injective
    rw [hbase, map_one, invK.apply_symm_apply]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact invK.left_inv x.1
  right_inv y := by
    apply Subtype.ext
    exact invK.right_inv y.1
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul invK x.1 y.1

/-- Under the local invariant and base-change formula, categorical degree-two
cohomology is explicitly the cyclic group of order `[L : K]`. -/
noncomputable def cohomologyZMod
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L) :
    groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ≃+
      ZMod (Module.finrank K L) := by
  let n := Module.finrank K L
  letI : NeZero n :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let e : Multiplicative
          (groupCohomology.H2
            (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) ≃*
        Multiplicative (localInvariantTorsion n) :=
    (multiplicativeHCohomology
        (G := Gal(L/K)) (M := Lˣ)).symm |>.trans
      (CProduc.hRelativeBrauer K L) |>.trans
      (relativeBrauerTorsion K L invK invL hbase) |>.trans
      (invariantTorsionPow n).symm
  exact e.toAdditive.trans (torsionZMod n).symm

/-- The finite local fundamental class is the class with invariant
`1 / [L : K]`, represented as `1` in `ZMod [L : K]`. -/
noncomputable def localFundamentalClass
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L) :
    groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) :=
  (cohomologyZMod K L invK invL hbase).symm 1

/-- Every finite local degree-two cohomology class is an integral multiple
of the fundamental class.  This is the generator input in Tate's theorem. -/
theorem zmultiples_fundamental_class
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L)
    (x : groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    x ∈ AddSubgroup.zmultiples
      (localFundamentalClass K L invK invL hbase) := by
  let e := cohomologyZMod K L invK invL hbase
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨ZMod.cast (e x), ?_⟩
  apply e.injective
  simp [e, localFundamentalClass]

omit [IsGalois K L] in
/-- The relative Brauer group of a finite local extension has cardinality
equal to the extension degree, conditional only on base change for the local
invariant. -/
theorem relative_brauer_finrank
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L) :
    Nat.card (relativeBrauerGroup K L) = Module.finrank K L := by
  let n := Module.finrank K L
  letI : NeZero n :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let eT : Multiplicative (localInvariantTorsion n) ≃*
      invariantPowTorsion n :=
    invariantTorsionPow n
  calc
    Nat.card (relativeBrauerGroup K L) =
        Nat.card (invariantPowTorsion n) :=
      Nat.card_congr
        (relativeBrauerTorsion K L invK invL hbase)
    _ = Nat.card (Multiplicative (localInvariantTorsion n)) :=
      (Nat.card_congr eT.toEquiv).symm
    _ = Nat.card (Multiplicative (ZMod n)) :=
      (Nat.card_congr
        (torsionZMod n).toMultiplicative.toEquiv).symm
    _ = n := Nat.card_zmod n

/-- The categorical `H²` of the multiplicative group of a finite Galois
local extension has cardinality equal to its degree.  This is the numerical
input in Theorem III.3.1. -/
theorem cohomology_units_finrank
    (invK : BrauerGroup K ≃* Multiplicative LocalInvariant)
    (invL : BrauerGroup L ≃* Multiplicative LocalInvariant)
    (hbase : ∀ x : BrauerGroup K,
      invL (brauerBaseChange K L x) = invK x ^ Module.finrank K L) :
    Nat.card
        (groupCohomology.H2
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) =
      Module.finrank K L := by
  calc
    Nat.card
        (groupCohomology.H2
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) =
        Nat.card
          (Multiplicative
            (groupCohomology.H2
              (Rep.ofMulDistribMulAction Gal(L/K) Lˣ))) := rfl
    _ = Nat.card (MHTwo Gal(L/K) Lˣ) :=
      (Nat.card_congr
        (multiplicativeHCohomology
          (G := Gal(L/K)) (M := Lˣ)).toEquiv).symm
    _ = Nat.card (relativeBrauerGroup K L) :=
      Nat.card_congr
        (CProduc.hRelativeBrauer K L).toEquiv
    _ = Module.finrank K L :=
      relative_brauer_finrank K L invK invL hbase

end

end Submission.CField.LBrauer
