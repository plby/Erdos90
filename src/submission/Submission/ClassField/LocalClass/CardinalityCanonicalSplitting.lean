import Submission.ClassField.LocalClass.CanonicalClassReduction

/-!
# Cardinality from splitting the canonical degree class

This is the finite-cardinality conclusion behind Milne III.2.2 and III.2.6.
If a degree-`n` extension splits the canonical local Brauer class of invariant
`1 / n`, then the relative Brauer group contains all `n`-torsion.  Conversely,
Corollary IV.3.17 says every relative class is killed by `n`, so the canonical
local invariant embeds the relative group back into that same finite torsion
group.  The two injections force cardinality `n`.
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

local instance relativeDegreeNeZero : NeZero (Module.finrank K L) :=
  ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩

/-- Splitting the canonical degree class forces the relative Brauer group to
have exactly the extension degree as its cardinality. -/
theorem relative_brauer_class
    (hcanonical : canonicalBrauerClass K (Module.finrank K L) ∈
      relativeBrauerGroup K L) :
    Nat.card (relativeBrauerGroup K L) = Module.finrank K L := by
  let n := Module.finrank K L
  let T := invariantPowTorsion n
  let eT : Multiplicative (ZMod n) ≃* T :=
    (torsionZMod n).toMultiplicative.trans
      (invariantTorsionPow n)
  let toRelative :=
    torsionBrauerCanonical
      K L n hcanonical
  let toTorsion := brauerInvariantTorsion K L
  have hToRelative : Function.Injective toRelative :=
    torsion_relative_injective
      K L n hcanonical
  have hToTorsion : Function.Injective toTorsion := by
    intro x y hxy
    apply Subtype.ext
    apply (carryBrauerInvariant K).injective
    simpa [toTorsion, brauerInvariantTorsion] using
      congrArg Subtype.val hxy
  letI : Finite T := Finite.of_injective eT.symm eT.symm.injective
  letI : Finite (relativeBrauerGroup K L) :=
    Finite.of_injective toTorsion hToTorsion
  have hTcard : Nat.card T = n := by
    calc
      Nat.card T = Nat.card (Multiplicative (ZMod n)) :=
        (Nat.card_congr eT.toEquiv).symm
      _ = n := Nat.card_zmod n
  apply Nat.le_antisymm
  · calc
      Nat.card (relativeBrauerGroup K L) ≤ Nat.card T :=
        Nat.card_le_card_of_injective toTorsion hToTorsion
      _ = Module.finrank K L := hTcard
  · calc
      Module.finrank K L = Nat.card T := hTcard.symm
      _ ≤ Nat.card (relativeBrauerGroup K L) :=
        Nat.card_le_card_of_injective toRelative hToRelative

/-- The equivalent categorical degree-two cohomology cardinality. -/
theorem cohomology_units_class
    (hcanonical : canonicalBrauerClass K (Module.finrank K L) ∈
      relativeBrauerGroup K L) :
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
      Nat.card_congr (CProduc.hRelativeBrauer K L).toEquiv
    _ = Module.finrank K L :=
      relative_brauer_class
        K L hcanonical

/-- Under the same splitting assertion, degree-two cohomology is the cyclic
group of the extension degree.  This strengthens the subgroup conclusion of
Lemma III.2.2 and supplies the exact group used in Lemma III.2.6. -/
noncomputable def cohomologyUnitsZ
    (hcanonical : canonicalBrauerClass K (Module.finrank K L) ∈
      relativeBrauerGroup K L) :
    groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ≃+
      ZMod (Module.finrank K L) := by
  let n := Module.finrank K L
  let hcard :=
    relative_brauer_class
      K L hcanonical
  exact
    (cohomologyTorsionCardinality
        K L hcard).trans
      ((invariantTorsionPow n).symm.toAdditive.trans
        (torsionZMod n).symm)

end

section CanonicalLocalStatement

noncomputable section

open BGroups CProduca LBrauer

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance canonicalStatementValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance canonicalStatementValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

local instance canonicalStatementDegreeNeZero :
    NeZero (Module.finrank K L) :=
  ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩

/-- Source-facing cardinality consequence with the norm-induced valuation
relation installed internally. -/
theorem cohomology_h_units
    (hcanonical : canonicalBrauerClass K (Module.finrank K L) ∈
      relativeBrauerGroup K L) :
    Nat.card
        (groupCohomology.H2
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) =
      Module.finrank K L :=
  cohomology_units_class
    K L hcanonical

/-- Source-facing cyclic coordinate on finite local degree-two cohomology. -/
noncomputable def cohomology_units_z
    (hcanonical : canonicalBrauerClass K (Module.finrank K L) ∈
      relativeBrauerGroup K L) :
    groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ≃+
      ZMod (Module.finrank K L) :=
  cohomologyUnitsZ
    K L hcanonical

end

end CanonicalLocalStatement

end Submission.CField.LClass
