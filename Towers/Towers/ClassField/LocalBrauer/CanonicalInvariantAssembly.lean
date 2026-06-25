import Towers.ClassField.LocalBrauer.FiniteExtensionData
import Towers.ClassField.LocalBrauer.CofinalityUnconditional
import Towers.ClassField.LocalBrauer.FiniteInvariantCompatibility
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedData

/-!
# The local invariant on the canonical factorial tower

This file specializes the finite unramified invariant and the abstract
direct-limit assembly to the canonical factorial tower.  The finite fields
are equipped with their canonical spectral local-field structures.  The
remaining inputs are precisely the arithmetic residue-norm congruences, the
restriction formula for normalized order, and compatibility of the chosen
carry classes under inflation.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups CProduca

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev canonicalFactorialField (r : ℕ) :=
  unramifiedFactorialLevel K r

local instance canonicalFactorialAlgebraic (r : ℕ) :
    Algebra.IsAlgebraic K (canonicalFactorialField K r) :=
  Algebra.IsAlgebraic.of_finite K (canonicalFactorialField K r)

local instance canonicalFactorialNontriviallyNormedField (r : ℕ) :
    NontriviallyNormedField (canonicalFactorialField K r) :=
  FLExt.nontriviallyNormedField K
    (canonicalFactorialField K r)

local instance canonicalFactorialNormedAlgebra (r : ℕ) :
    NormedAlgebra K (canonicalFactorialField K r) :=
  spectralNorm.normedAlgebra K (canonicalFactorialField K r)

local instance canonicalFactorialIsUltrametricDist (r : ℕ) :
    IsUltrametricDist (canonicalFactorialField K r) :=
  IsUltrametricDist.of_normedAlgebra K

local instance canonicalFactorialValuativeRel (r : ℕ) :
    ValuativeRel (canonicalFactorialField K r) :=
  FLExt.valuativeRel K (canonicalFactorialField K r)

local instance canonicalFactorialValuationCompatible (r : ℕ) :
    Valuation.Compatible
      (NormedField.valuation (K := canonicalFactorialField K r)) :=
  Valuation.Compatible.ofValuation
    (NormedField.valuation (K := canonicalFactorialField K r))

local instance canonicalFactorialIsLocalField (r : ℕ) :
    IsNonarchimedeanLocalField (canonicalFactorialField K r) :=
  FLExt.nonarchimedeanLocalField K
    (canonicalFactorialField K r)

local instance canonicalFactorialDegreeNeZero (r : ℕ) :
    NeZero (invariantLevelDegree r) :=
  ⟨(invariant_level_pos r).ne'⟩

/-- The cyclic model of the Galois group at a canonical factorial level. -/
def factorialGalZ (r : ℕ) :
    Multiplicative (ZMod (invariantLevelDegree r)) ≃*
      Gal(canonicalFactorialField K r/K) :=
  galZMod K
    (invariantLevelDegree r)

/-- A simultaneous choice of cyclic coordinates on all factorial levels. -/
abbrev FactorialGalFamily := ∀ r : ℕ,
  Multiplicative (ZMod (invariantLevelDegree r)) ≃*
    Gal(canonicalFactorialField K r/K)

/-- A fixed normalized uniformizer of the base local field. -/
def canonicalLocalUniformizer : Kˣ :=
  Classical.choose (local_order_surjective K 1)

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
@[simp] theorem canonical_uniformizer_order :
    localUnitOrder K
      (Additive.ofMul (canonicalLocalUniformizer K)) = 1 :=
  Classical.choose_spec (local_order_surjective K 1)

/-- Compatibility of a simultaneous cyclic coordinate choice with
inflation of Milne's carry classes. -/
def FactorialCarryInflation
    (eGal : FactorialGalFamily K) : Prop :=
  ∀ r s (h : r ≤ s),
    inflationHom K (factorial_level_monotone K h)
        (unramifiedCarryH K (canonicalFactorialField K r)
          (eGal r) (canonicalLocalUniformizer K)) =
      (unramifiedCarryH K (canonicalFactorialField K s)
        (eGal s) (canonicalLocalUniformizer K)) ^
          (invariantLevelDegree s / invariantLevelDegree r)

/-- The residue algebra, unit-norm approximation, and normalized-order
restriction used at every level of the canonical factorial tower. -/
structure FIData : Type u where
  residueAlgebra (r : ℕ) :
    Algebra 𝓀[K] 𝓀[canonicalFactorialField K r]
  unitNormData (r : ℕ) :
    letI := residueAlgebra r
    UnramifiedUnitData K (canonicalFactorialField K r)
      (FLExt.integerUnitNorm K
        (canonicalFactorialField K r))
  order_algebraMap (r : ℕ) (x : Kˣ) :
    localUnitOrder (canonicalFactorialField K r)
        (Additive.ofMul (Units.map
          (algebraMap K (canonicalFactorialField K r)) x)) =
      localUnitOrder K (Additive.ofMul x)

private theorem factorial_level_data (r : ℕ) :
    ∃ hResidueAlgebra : Algebra 𝓀[K] 𝓀[canonicalFactorialField K r],
      letI : Algebra 𝓀[K] 𝓀[canonicalFactorialField K r] :=
        hResidueAlgebra
      UnramifiedUnitData K (canonicalFactorialField K r)
          (FLExt.integerUnitNorm K
            (canonicalFactorialField K r)) ∧
        ∀ x : Kˣ,
          localUnitOrder (canonicalFactorialField K r)
              (Additive.ofMul (Units.map
                (algebraMap K (canonicalFactorialField K r)) x)) =
            localUnitOrder K (Additive.ofMul x) := by
  obtain ⟨hResidueAlgebra, hUnit, horder, _⟩ :=
    unramified_level_data K
      (invariantLevelDegree r)
  exact ⟨hResidueAlgebra, hUnit, horder⟩

@[implicit_reducible]
private noncomputable def canonicalFactorialAlgebra (r : ℕ) :
    Algebra 𝓀[K] 𝓀[canonicalFactorialField K r] :=
  Classical.choose (factorial_level_data K r)

private theorem canonicalFactorialData (r : ℕ) :
    letI : Algebra 𝓀[K] 𝓀[canonicalFactorialField K r] :=
      canonicalFactorialAlgebra K r
    UnramifiedUnitData K (canonicalFactorialField K r)
      (FLExt.integerUnitNorm K
        (canonicalFactorialField K r)) :=
  (Classical.choose_spec
    (factorial_level_data K r)).1

private theorem canonical_factorial_algebra (r : ℕ) (x : Kˣ) :
    localUnitOrder (canonicalFactorialField K r)
        (Additive.ofMul (Units.map
          (algebraMap K (canonicalFactorialField K r)) x)) =
      localUnitOrder K (Additive.ofMul x) :=
  (Classical.choose_spec
    (factorial_level_data K r)).2 x

/-- The canonical factorial tower carries the arithmetic norm and order data
needed by the finite local invariants, with no additional hypotheses. -/
noncomputable def factorialInvariantData :
    FIData K where
  residueAlgebra := canonicalFactorialAlgebra K
  unitNormData := canonicalFactorialData K
  order_algebraMap := canonical_factorial_algebra K

/-- A compatible family of finite invariants on the canonical factorial
tower.  Packaging the family prevents later assembly from unfolding the
spectral local-field construction. -/
structure CanonicalFactorialSystem : Type (u + 1) where
  equiv (r : ℕ) :
    brauerCofinalLevel K (unramifiedFactorialLevel K) r ≃*
      invariantTorsionLevel r
  compatible : ∀ r s h x,
    equiv s (brauerCofinalInclusion K
        (unramifiedFactorialLevel K)
        (factorial_level_monotone K) r s h x) =
      invariantTorsionInclusion r s h (equiv r x)

/-- A compatible finite-invariant system on the canonical cofinal tower
assembles unconditionally to an invariant on the absolute Brauer group. -/
def assembleFactorialInvariant
    (S : CanonicalFactorialSystem K)
    (hcofinal : ∀ x : BrauerGroup K,
      ∃ r, x ∈ relativeBrauerGroup K
        (unramifiedFactorialLevel K r)) :
    BrauerGroup K ≃* Multiplicative LocalInvariant :=
  localBrauerInvariant
    (K := K)
    (L := unramifiedFactorialLevel K)
    (hL := factorial_level_monotone K)
    (e := S.equiv)
    (he := S.compatible)
    (hcofinal := hcofinal)

/-- The abstract canonical assembly restricts to its finite-level system. -/
@[simp]
theorem assemble_factorial_coe
    (S : CanonicalFactorialSystem K)
    (hcofinal : ∀ x : BrauerGroup K,
      ∃ r, x ∈ relativeBrauerGroup K
        (unramifiedFactorialLevel K r)) (r : ℕ)
    (x : brauerCofinalLevel K (unramifiedFactorialLevel K) r) :
    assembleFactorialInvariant K S hcofinal
        (x : BrauerGroup K) =
      invariantTorsionMul r (S.equiv r x) :=
  brauer_invariant_coe
    (K := K)
    (L := unramifiedFactorialLevel K)
    (hL := factorial_level_monotone K)
    (e := S.equiv)
    (he := S.compatible)
    (hcofinal := hcofinal) r x

namespace FIData

/-- The carry class at the `r`-th canonical factorial level. -/
def carry (eGal : FactorialGalFamily K) (r : ℕ) :
    brauerCofinalLevel K (unramifiedFactorialLevel K) r :=
  unramifiedCarryRelative K
    (canonicalFactorialField K r)
    (eGal r)
    (canonicalLocalUniformizer K)

variable (d : FIData K)

/-- The full local norm data obtained from the residue congruences. -/
theorem localNormData (r : ℕ) :
    letI := FIData.residueAlgebra d r
    UnramifiedLocalData K (canonicalFactorialField K r)
      (FLExt.integerUnitNorm K
        (canonicalFactorialField K r)) := by
  letI := FIData.residueAlgebra d r
  exact FLExt.unramified_data_unit K
    (canonicalFactorialField K r)
    (FIData.residueAlgebra d r)
    (FIData.unitNormData d r)

include d in
/-- Field norm multiplies normalized order by the factorial-level degree. -/
theorem order_norm (r : ℕ) (x : (canonicalFactorialField K r)ˣ) :
    localUnitOrder K
        (Additive.ofMul (localNormUnits K
          (canonicalFactorialField K r) x)) =
      (invariantLevelDegree r : ℤ) *
        localUnitOrder (canonicalFactorialField K r)
          (Additive.ofMul x) := by
  rw [show localNormUnits K (canonicalFactorialField K r) x =
      Units.map (Algebra.norm K) x by rfl]
  apply UOExt.order_norm_finrankeq K
    (canonicalFactorialField K r)
  · exact
      { order_algebraMap :=
          FIData.order_algebraMap d r
        order_aut := FLExt.unit_order_aut K
          (canonicalFactorialField K r) }
  · exact factorial_level_finrank K r

/-- The finite invariant at the `r`-th canonical factorial level. -/
def finiteInvariant (eGal : FactorialGalFamily K) (r : ℕ) :
    brauerCofinalLevel K (unramifiedFactorialLevel K) r ≃*
      invariantTorsionLevel r := by
  letI := FIData.residueAlgebra d r
  exact unramifiedInvariantEquiv K
    (canonicalFactorialField K r)
    (eGal r)
    (by simp [invariantLevelDegree])
    (FLExt.integerUnitNorm K
      (canonicalFactorialField K r))
    (localNormData K d r)
    (order_norm K d r)

include d in
/-- Every finite-level relative Brauer class is a power of the carry class. -/
theorem carry_pow
    (eGal : FactorialGalFamily K) (r : ℕ)
    (x : brauerCofinalLevel K (unramifiedFactorialLevel K) r) :
    ∃ i : ℕ, x = (carry K eGal r) ^ i := by
  letI := FIData.residueAlgebra d r
  obtain ⟨i, hi⟩ := unramified_carry_brauer K
    (canonicalFactorialField K r)
    (eGal r)
    (by simp [invariantLevelDegree])
    (FLExt.integerUnitNorm K
      (canonicalFactorialField K r))
    (localNormData K d r)
    (order_norm K d r)
    (canonicalLocalUniformizer K)
    (canonical_uniformizer_order K) x
  exact ⟨i.val, hi⟩

/-- The finite invariant sends the carry class to `1 / (r + 2)!`. -/
theorem finiteInvariant_carry
    (eGal : FactorialGalFamily K) (r : ℕ) :
    finiteInvariant K d eGal r (carry K eGal r) =
      Multiplicative.ofAdd
        (localDivTorsion (invariantLevelDegree r)) := by
  letI := FIData.residueAlgebra d r
  exact unramified_equiv_carry K
    (canonicalFactorialField K r)
    (eGal r)
    (by simp [invariantLevelDegree])
    (FLExt.integerUnitNorm K
      (canonicalFactorialField K r))
    (localNormData K d r)
    (order_norm K d r)
    (canonicalLocalUniformizer K)
    (canonical_uniformizer_order K)

/-- The canonical factorial finite invariants commute with inclusion. -/
theorem finiteInvariant_compatible
    (eGal : FactorialGalFamily K)
    (hinflation : FactorialCarryInflation K eGal) :
    ∀ (r s : ℕ) (h : r ≤ s)
      (x : brauerCofinalLevel K (unramifiedFactorialLevel K) r),
      finiteInvariant K d eGal s
          (brauerCofinalInclusion K
            (unramifiedFactorialLevel K)
            (factorial_level_monotone K) r s h x) =
        invariantTorsionInclusion r s h
          (finiteInvariant K d eGal r x) := by
  apply factorial_compatibility_carry K
    (finiteInvariant K d eGal)
    (fun r ↦ unramifiedCarryH K (canonicalFactorialField K r)
      (eGal r)
      (canonicalLocalUniformizer K))
  · intro r x
    exact carry_pow K d eGal r x
  · intro r
    exact finiteInvariant_carry K d eGal r
  · exact hinflation

/-- The explicit finite invariants and their carry compatibility, packaged
without unfolding their spectral local-field construction. -/
def finiteInvariantSystem (d : FIData K)
    (eGal : FactorialGalFamily K)
    (hinflation : FactorialCarryInflation K eGal) :
    CanonicalFactorialSystem K where
  equiv := finiteInvariant K d eGal
  compatible := finiteInvariant_compatible K d eGal hinflation

end FIData

end

end Towers.CField.LBrauer
