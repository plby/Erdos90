import Submission.ClassField.CrossedProducts.IsMulCoboundary
import Submission.ClassField.LocalBrauer.CanonicalCarryUnconditional
import Submission.ClassField.LocalBrauer.H2Cardinality
import Submission.ClassField.LocalBrauer.UnramifiedFiniteInvariant

/-!
# Finite relative invariants from cardinality

For a finite Galois extension of local fields, Corollary IV.3.17 shows that
the relative Brauer group is killed by the extension degree.  If its
cardinality is that degree, injectivity of the canonical local invariant
therefore identifies it with the full degree-torsion subgroup of `ℚ / ℤ`.

This argument does not use the local-invariant base-change formula.  It is
the bridge from the cardinality conclusion of Lemma III.2.6 to the canonical
finite fundamental class used after Theorem III.2.1.
-/

namespace Submission.CField.LClass

noncomputable section

open BGroups CProduca LBrauer

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

local instance finiteRelativeDegreeNeZero : NeZero (Module.finrank K L) :=
  ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩

/-- Restriction of the canonical local invariant to the relative Brauer
group, with codomain restricted to the subgroup killed by the extension
degree. -/
noncomputable def brauerInvariantTorsion :
    relativeBrauerGroup K L →*
      invariantPowTorsion (Module.finrank K L) where
  toFun x := ⟨carryBrauerInvariant K (x : BrauerGroup K), by
    change (carryBrauerInvariant K (x : BrauerGroup K)) ^
      Module.finrank K L = 1
    rw [← map_pow]
    have hx : (x : BrauerGroup K) ^ Module.finrank K L = 1 := by
      simpa using congrArg Subtype.val
        (relative_brauer_one K L x)
    rw [hx, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (carryBrauerInvariant K)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (carryBrauerInvariant K) x.1 y.1

/-- If the relative Brauer group has the expected cardinality, its
restricted canonical invariant is an equivalence onto the full
degree-torsion subgroup of `ℚ / ℤ`. -/
noncomputable def relativeTorsionCardinality
    (hcard : Nat.card (relativeBrauerGroup K L) = Module.finrank K L) :
    relativeBrauerGroup K L ≃*
      invariantPowTorsion (Module.finrank K L) := by
  let n := Module.finrank K L
  letI : NeZero n :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let f := brauerInvariantTorsion K L
  let eT : Multiplicative (ZMod n) ≃*
      invariantPowTorsion n :=
    (torsionZMod n).toMultiplicative.trans
      (invariantTorsionPow n)
  letI : Finite (relativeBrauerGroup K L) :=
    Nat.finite_of_card_ne_zero <| by
      rw [hcard]
      exact NeZero.ne n
  letI : Finite (invariantPowTorsion n) :=
    Finite.of_injective eT.symm eT.symm.injective
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply (carryBrauerInvariant K).injective
    exact congrArg Subtype.val hxy
  have hcards : Nat.card (relativeBrauerGroup K L) =
      Nat.card (invariantPowTorsion n) := by
    calc
      Nat.card (relativeBrauerGroup K L) = n := hcard
      _ = Nat.card (Multiplicative (ZMod n)) := (Nat.card_zmod n).symm
      _ = Nat.card (invariantPowTorsion n) :=
        Nat.card_congr eT.toEquiv
  exact MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).2 ⟨hf, hcards⟩)

/-- The element `1 / n` in the multiplicative degree-`n` torsion target. -/
noncomputable def invariantDivTorsion
    (n : ℕ) [NeZero n] : invariantPowTorsion n :=
  invariantTorsionPow n
    (Multiplicative.ofAdd (localDivTorsion n))

@[simp]
theorem div_torsion_coe
    (n : ℕ) [NeZero n] :
    (invariantDivTorsion n :
        Multiplicative LocalInvariant) =
      Multiplicative.ofAdd
        ((1 : ℚ) / (n : ℚ) : LocalInvariant) := by
  apply Multiplicative.ext
  exact invariant_div_coe n

/-- The unique relative Brauer class whose canonical invariant is
`1 / [L : K]`, constructed using only the expected cardinality. -/
noncomputable def relativeFundamentalCardinality
    (hcard : Nat.card (relativeBrauerGroup K L) = Module.finrank K L) :
    relativeBrauerGroup K L :=
  (relativeTorsionCardinality K L hcard).symm
    (invariantDivTorsion (Module.finrank K L))

@[simp]
theorem canonical_fundamental_cardinality
    (hcard : Nat.card (relativeBrauerGroup K L) = Module.finrank K L) :
    carryBrauerInvariant K
        (relativeFundamentalCardinality K L hcard : BrauerGroup K) =
      Multiplicative.ofAdd
        ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) := by
  let n := Module.finrank K L
  letI : NeZero n :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  let e := relativeTorsionCardinality K L hcard
  have h := congrArg Subtype.val
    (e.apply_symm_apply (invariantDivTorsion n))
  simpa only [relativeFundamentalCardinality,
    relativeTorsionCardinality,
    brauerInvariantTorsion,
    div_torsion_coe] using h

/-- Characterization and uniqueness of the relative fundamental class. -/
theorem relative_class_cardinality
    (hcard : Nat.card (relativeBrauerGroup K L) = Module.finrank K L)
    (x : relativeBrauerGroup K L) :
    x = relativeFundamentalCardinality K L hcard ↔
      carryBrauerInvariant K (x : BrauerGroup K) =
        Multiplicative.ofAdd
          ((1 : ℚ) / (Module.finrank K L : ℚ) : LocalInvariant) := by
  constructor
  · rintro rfl
    exact canonical_fundamental_cardinality K L hcard
  · intro hx
    apply Subtype.ext
    apply (carryBrauerInvariant K).injective
    exact hx.trans
      (canonical_fundamental_cardinality K L hcard).symm

/-- The cardinality-based equivalence transported through normalized
multiplicative `H²` and then through Mathlib's categorical `H²`. -/
noncomputable def cohomologyTorsionCardinality
    (hcard : Nat.card (relativeBrauerGroup K L) = Module.finrank K L) :
    groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ≃+
      Additive (invariantPowTorsion (Module.finrank K L)) :=
  ((multiplicativeHCohomology
      (G := Gal(L/K)) (M := Lˣ)).symm.trans
    ((CProduc.hRelativeBrauer K L).trans
      (relativeTorsionCardinality K L hcard))).toAdditive

/-- The finite local fundamental class in categorical degree-two
cohomology, obtained from the cardinality-based relative Brauer class. -/
noncomputable def cohomologyFundamentalCardinality
    (hcard : Nat.card (relativeBrauerGroup K L) = Module.finrank K L) :
    groupCohomology.H2 (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) :=
  (cohomologyTorsionCardinality K L hcard).symm
    (Additive.ofMul
      (invariantDivTorsion (Module.finrank K L)))

@[simp]
theorem h_fundamental_cardinality
    (hcard : Nat.card (relativeBrauerGroup K L) = Module.finrank K L) :
    cohomologyTorsionCardinality K L hcard
        (cohomologyFundamentalCardinality K L hcard) =
      Additive.ofMul
        (invariantDivTorsion (Module.finrank K L)) :=
  (cohomologyTorsionCardinality K L hcard).apply_symm_apply _

/-- The categorical fundamental class is the unique class sent to `1 / n`
by the transported finite relative invariant. -/
theorem cohomology_fundamental_cardinality
    (hcard : Nat.card (relativeBrauerGroup K L) = Module.finrank K L)
    (x : groupCohomology.H2
      (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) :
    x = cohomologyFundamentalCardinality K L hcard ↔
      cohomologyTorsionCardinality K L hcard x =
        Additive.ofMul
          (invariantDivTorsion (Module.finrank K L)) := by
  let e := cohomologyTorsionCardinality K L hcard
  constructor
  · rintro rfl
    exact h_fundamental_cardinality K L hcard
  · intro hx
    apply e.injective
    exact hx.trans
      (h_fundamental_cardinality K L hcard).symm

end

end Submission.CField.LClass
