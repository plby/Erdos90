import Submission.ClassField.LocalClass.FiniteRelativeCardinality
import Submission.ClassField.LocalClass.CardinalityCanonicalSplitting
import Submission.ClassField.LocalClass.FiniteGaloisExtensions
import Submission.ClassField.LocalClass.AbsoluteInvariant
import Submission.ClassField.LocalClass.ScratchTransportSetup
import Submission.ClassField.LocalBrauer.InvariantGaloisKernel

/-!
# Milne, Class Field Theory, Theorem III.2.1

This file gives the source-facing pieces of the local invariant theorem.
The absolute second cohomology group is the finite-Galois direct limit of
Corollary IV.3.16, not an abbreviation for the Brauer group.  Restriction
between absolute groups is transported from the genuine Brauer scalar
extension map.

For a finite Galois extension, Lemmas III.2.2--2.6 identify relative `H²`
with the subgroup `(1/n)ℤ/ℤ` of the absolute target.  We use the equivalent
models `ZMod n` and the subgroup of `ℚ/ℤ` killed by `n`.
-/

namespace Submission.CField.LClass

noncomputable section

universe u

open BGroups CProduca LBrauer

section AbsoluteInvariant

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance absoluteH2RestrictionSourceValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance absoluteH2RestrictionSourceValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]

set_option synthInstance.maxHeartbeats 100000 in
-- Resolving the absolute cohomology direct-limit equivalence requires a deeper
-- instance search than Lean's default.
/-- **Theorem III.2.1, first assertion.**  The canonical invariant on
absolute multiplicative degree-two cohomology of a local field.  The target
`Multiplicative LocalInvariant` is multiplicative notation for `ℚ/ℤ`.

The valuation relation and compatibility instance are canonical and are
installed internally rather than exposed as hypotheses. -/
noncomputable def absoluteInvariant :
    absoluteMultiplicativeH K ≃* Multiplicative LocalInvariant :=
  absoluteHInvariant K

end AbsoluteInvariant

section AbsoluteRestriction

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

set_option maxHeartbeats 1000000 in
-- The two dependent direct-limit equivalences have deeply nested instance terms.
set_option synthInstance.maxHeartbeats 100000 in
/-- Restriction on Milne's absolute `H²`, defined by the cohomology--Brauer
comparison and genuine scalar extension of central simple algebras. -/
noncomputable def absoluteHRestriction :
    absoluteMultiplicativeH K →* absoluteMultiplicativeH L :=
  (brauerAbsoluteMultiplicative L).toMonoidHom.comp
    ((brauerBaseChange K L).comp
      (brauerAbsoluteMultiplicative K).symm.toMonoidHom)

set_option synthInstance.maxHeartbeats 100000 in
-- Simplifying the two dependent direct-limit equivalences requires additional
-- instance-search time.
/-- The definition of absolute restriction has exactly the expected
interpretation on the Brauer side. -/
@[simp]
theorem absolute_brauer_restriction
    (x : absoluteMultiplicativeH K) :
    absoluteHBrauer L (absoluteHRestriction K L x) =
      brauerBaseChange K L (absoluteHBrauer K x) := by
  change (brauerAbsoluteMultiplicative L).symm
      ((brauerAbsoluteMultiplicative L)
        (brauerBaseChange K L
          ((brauerAbsoluteMultiplicative K).symm x))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end AbsoluteRestriction

section FiniteRelativeInvariant

variable (K L : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance finiteValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance finiteValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

local instance finiteDegreeNeZero :
    NeZero (Module.finrank K L) :=
  ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩

/-- The finite relative invariant in the literal `(1/n)ℤ/ℤ` model: the
subgroup of `ℚ/ℤ` killed by `n = [L:K]`.  Its underlying map is restriction
of the canonical absolute local invariant to the relative Brauer group. -/
noncomputable def relativeHTorsion :
    MHTwo Gal(L/K) Lˣ ≃*
      invariantPowTorsion (Module.finrank K L) :=
  (CProduc.hRelativeBrauer K L).trans
    (relativeTorsionCardinality K L
      (relative_brauer_class
        K L (brauer_relative_galois K L)))

/-- Under the finite relative invariant, forgetting the torsion proof gives
the canonical local invariant of the corresponding relative Brauer class. -/
@[simp]
theorem invariant_torsion_coe
    (x : MHTwo Gal(L/K) Lˣ) :
    ((relativeHTorsion K L x :
        invariantPowTorsion (Module.finrank K L)) :
      Multiplicative LocalInvariant) =
      carryBrauerInvariant K
        ((CProduc.hRelativeBrauer K L x :
          relativeBrauerGroup K L) : BrauerGroup K) := by
  rfl

/-- **Theorem III.2.1, finite assertion.**  For a finite Galois extension
of degree `n`, relative degree-two cohomology is canonically `ZMod n`, the
standard finite model of `(1/n)ℤ/ℤ`. -/
noncomputable def invariantZMod :
    groupCohomology.H2
        (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ≃+
      ZMod (Module.finrank K L) :=
  cohomology_units_z
    K L (brauer_relative_galois K L)

/-- The finite invariant is an isomorphism, hence in particular the
canonical inclusion `(1/n)ℤ/ℤ → H²(L/K)` of Lemma III.2.2 is onto. -/
theorem invariant_z_bijective :
    Function.Bijective (invariantZMod K L) :=
  (invariantZMod K L).bijective

end FiniteRelativeInvariant

section FiniteLevelInAbsolute

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

local instance levelValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance levelValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K))

local instance levelDegreeNeZero :
    NeZero (Module.finrank K E) :=
  ⟨(Module.finrank_pos (R := K) (M := E)).ne'⟩

set_option maxHeartbeats 1000000 in
-- Equality in the dependent direct limit is compared through the Brauer model.
set_option synthInstance.maxHeartbeats 100000 in
omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] in
/-- A finite relative `H²` group embeds in absolute `H²` by the canonical
map into the direct limit. -/
theorem absolute_multiplicative_injective :
    Function.Injective (absoluteMultiplicative2 K E) := by
  intro x y hxy
  apply (CProduc.hRelativeBrauer K E).injective
  apply Subtype.ext
  have h := congrArg (absoluteHBrauer K) hxy
  simpa only [absolute_brauer_multiplicative] using h

set_option maxHeartbeats 1000000 in
-- Both sides unfold the finite-level comparison inside the absolute limit.
set_option synthInstance.maxHeartbeats 100000 in
/-- The absolute invariant restricted to a finite Galois level is exactly
the finite `(1/n)ℤ/ℤ` invariant constructed above. -/
theorem absolute_multiplicative_2
    (x : MHTwo Gal(E/K) Eˣ) :
    absoluteInvariant K (absoluteMultiplicative2 K E x) =
      (relativeHTorsion K E x :
        Multiplicative LocalInvariant) := by
  rw [absoluteInvariant,
    absolute_invariant_multiplicative]
  exact (invariant_torsion_coe K E x).symm

/-- Consequently the invariant of every finite-level class is killed by
the degree of that level, as in the left-hand part of Milne's diagram. -/
theorem absolute_multiplicative_h
    (x : MHTwo Gal(E/K) Eˣ) :
    (absoluteInvariant K
      (absoluteMultiplicative2 K E x)) ^ Module.finrank K E = 1 := by
  rw [absolute_multiplicative_2]
  exact (relativeHTorsion K E x).property

end FiniteLevelInAbsolute

section RestrictionFormula

variable (K L : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance formulaValuativeRelK : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance formulaValuationCompatibleK :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

set_option maxHeartbeats 1000000 in
-- Constructing the spectral invariant installs the complete canonical local
-- field structure on the abstract extension.
set_option synthInstance.maxHeartbeats 100000 in
-- Absolute cohomology is a dependent direct limit over finite Galois fields.
/-- The invariant on an abstract finite extension, using its canonical
spectral local-field topology internally. -/
noncomputable def spectralAbsoluteInvariant :
    absoluteMultiplicativeH L ≃* Multiplicative LocalInvariant :=
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    ValuativeRel.ofValuation (NormedField.valuation (K := L))
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  absoluteHInvariant L

set_option maxHeartbeats 1000000 in
-- Constructing the Brauer-side spectral invariant unfolds the same canonical
-- local-field and dependent-limit data.
set_option synthInstance.maxHeartbeats 100000 in
-- The canonical invariant unfolds the dependent factorial unramified tower.
/-- The same spectral local invariant on the Brauer-group model. -/
noncomputable def spectralCarryInvariant :
    BrauerGroup L ≃* Multiplicative LocalInvariant :=
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    ValuativeRel.ofValuation (NormedField.valuation (K := L))
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  carryBrauerInvariant L

set_option synthInstance.maxHeartbeats 100000 in
-- Both absolute cohomology groups are dependent direct limits.
/-- Milne's restriction square, expressed in the actual direct-limit model
of absolute `H²`.  In multiplicative notation the bottom map `q ↦ n q` is
the `n`th-power map. -/
def AbsoluteHFormula : Prop :=
  ∀ x : absoluteMultiplicativeH K,
    spectralAbsoluteInvariant K L (absoluteHRestriction K L x) =
      (absoluteInvariant K x) ^ Module.finrank K L

set_option maxHeartbeats 1000000 in
-- Comparing the cohomological and Brauer formulations unfolds both dependent
-- direct-limit equivalences.
set_option synthInstance.maxHeartbeats 100000 in
omit [IsGalois K L] in
-- Unfolding both direct-limit equivalences creates a deep definitional term.
/-- The absolute restriction formula is exactly the local Brauer invariant
base-change formula.  Thus no compatibility is hidden by the direct-limit
presentation. -/
theorem absolute_restriction_change :
    AbsoluteHFormula K L ↔
      ∀ b : BrauerGroup K,
        spectralCarryInvariant K L
            (brauerBaseChange K L b) =
          (carryBrauerInvariant K b) ^ Module.finrank K L := by
  constructor
  · intro h b
    let x := brauerAbsoluteMultiplicative K b
    have hx := h x
    simpa [AbsoluteHFormula, absoluteInvariant,
      spectralAbsoluteInvariant,
      spectralCarryInvariant,
      absoluteHInvariant, absoluteHRestriction, x] using hx
  · intro h x
    simpa [AbsoluteHFormula, absoluteInvariant,
      spectralAbsoluteInvariant,
      spectralCarryInvariant,
      absoluteHInvariant, absoluteHRestriction] using
      h ((brauerAbsoluteMultiplicative K).symm x)

set_option maxHeartbeats 2000000 in
-- Proving the restriction formula invokes the full spectral base-change
-- theorem and its large canonical instance tower.
set_option synthInstance.maxHeartbeats 200000 in
/-- **Theorem III.2.1, restriction formula.**  Absolute restriction on the
genuine finite-Galois direct limit multiplies the local invariant by the
extension degree. -/
theorem absoluteRestrictionFormula :
    AbsoluteHFormula K L := by
  apply (absolute_restriction_change K L).2
  intro b
  simpa [spectralCarryInvariant] using
    (change_formula_galois K L b)

set_option maxHeartbeats 1000000 in
-- Restriction and the absolute invariant both unfold maps on a dependent
-- direct limit in this relative-class calculation.
set_option synthInstance.maxHeartbeats 100000 in
-- The absolute invariant and restriction both unfold direct-limit maps.
/-- The required square is already unconditional on its finite relative
subgroup `H²(L/K)`: both sides vanish after restriction / multiplication by
the degree. -/
theorem absolute_restriction_relative
    (x : absoluteMultiplicativeH K)
    (hx : absoluteHBrauer K x ∈ relativeBrauerGroup K L) :
    spectralAbsoluteInvariant K L (absoluteHRestriction K L x) =
      (absoluteInvariant K x) ^ Module.finrank K L := by
  simpa [spectralAbsoluteInvariant,
    spectralCarryInvariant,
    absoluteInvariant, absoluteHInvariant,
    absoluteHRestriction] using
      (brauer_base_change
        K L (Multiplicative LocalInvariant)
        (carryBrauerInvariant K)
        (spectralCarryInvariant K L)
        (absoluteHBrauer K x) hx)

end RestrictionFormula

end

end Submission.CField.LClass
