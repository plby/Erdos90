import Towers.ClassField.NormCorrespondence.LocalStatements
import Towers.ClassField.NormCorrespondence.SubgroupOpenClosed
import Towers.ClassField.NormCorrespondence.LocalStatement
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedData
import Towers.ClassField.LocalBrauer.FiniteExtensionData
import Towers.ClassField.LocalBrauer.UnramifiedH2
import Towers.ClassField.LocalBrauer.UnramifiedNormOrder

/-!
# Norm groups of the canonical unramified extensions

For every positive `n`, the canonical unramified extension of degree `n` is
a finite abelian subextension of the chosen separable closure.  Its norm group
consists exactly of the elements of `Kˣ` whose normalized order is divisible
by `n`.  This is the unramified part of the construction used in the Local
Existence Theorem.
-/

namespace Towers.CField.LFTheory

noncomputable section

universe u

open ValuativeRel
open LBrauer

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The canonical unramified degree-`n` extension, bundled as a finite
abelian subextension of the chosen separable closure. -/
noncomputable def canonicalUnramifiedSubextension
    (n : ℕ) [NeZero n] : FASubext K where
  finiteIntermediateField := canonicalUnramifiedLevel K n
  isAbelian := by
    letI : IsCyclic Gal(canonicalUnramifiedLevel K n / K) :=
      unramified_level_cyclic K n
    exact IsCyclic.isMulCommutative

/-- The bundled canonical unramified subextension has degree `n`. -/
theorem unramified_subextension_finrank
    (n : ℕ) [NeZero n] :
    Module.finrank K (canonicalUnramifiedSubextension K n).1 = n :=
  unramified_level_finrank K n

set_option maxHeartbeats 1000000 in
-- Unpacking the spectral integral model has a deeply dependent instance telescope.
set_option synthInstance.maxHeartbeats 100000 in
/-- The canonical degree-`n` subextension is unramified in the intrinsic
sense used by the statement of the Local Recip Law. -/
theorem unramified_subextension
    (n : ℕ) [NeZero n] :
    (canonicalUnramifiedSubextension K n).IsUnramified K := by
  unfold FASubext.IsUnramified
  dsimp only [canonicalUnramifiedSubextension]
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    spectralValuationExtension K E
  let A := Valuation.integer (ValuativeRel.valuation K)
  let A0 := Valuation.integer (NormedField.valuation (K := K))
  let N := Valuation.integer (NormedField.valuation (K := E))
  letI : Algebra A N := valuativeSpectralAlgebra K E
  let eA := valuativeIntegerNorm K
  letI : Algebra A A0 := eA.toRingHom.toAlgebra
  letI : IsScalarTower A A0 N :=
    ⟨fun x y z ↦ by
      simp only [Algebra.smul_def, map_mul, mul_assoc]
      change _ = algebraMap A0 N (eA x) * _
      rfl⟩
  have hData := level_spectral_data K n
  letI : Module.Finite A N := hData.1
  letI : Algebra.FormallyUnramified A N := hData.2.1
  change Module.Finite A0 N ∧ Algebra.FormallyUnramified A0 N
  letI : Module.Finite A0 N :=
    Module.Finite.of_restrictScalars_finite A A0 N
  letI : Algebra.FormallyUnramified A0 N :=
    Algebra.FormallyUnramified.of_restrictScalars A A0 N
  exact ⟨inferInstance, inferInstance⟩

set_option maxHeartbeats 1000000 in
-- The canonical local-field structure has a deeply dependent instance telescope.
/-- The norm group of the canonical unramified degree-`n` extension is the
kernel of normalized order modulo `n`. -/
theorem unramified_level_ker
    (n : ℕ) [NeZero n] :
    normSubgroup K (canonicalUnramifiedLevel K n) =
      (localOrderMod K n).ker := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  obtain ⟨hResidueAlgebra, hUnit, horder, _⟩ :=
    unramified_level_data K n
  letI : Algebra 𝓀[K] 𝓀[E] := hResidueAlgebra
  have hLocal : UnramifiedLocalData K E
      (FLExt.integerUnitNorm K E) :=
    FLExt.unramified_data_unit
      K E hResidueAlgebra hUnit
  have hOrderNorm (x : Eˣ) :
      localUnitOrder K
          (Additive.ofMul (localNormUnits K E x)) =
        (n : ℤ) * localUnitOrder E (Additive.ofMul x) := by
    rw [show localNormUnits K E x =
        Units.map (Algebra.norm K) x by rfl]
    apply UOExt.order_norm_finrankeq K E
    · exact
        { order_algebraMap := horder
          order_aut := FLExt.unit_order_aut K E }
    · exact unramified_level_finrank K n
  change (localNormUnits K E).range =
    (localOrderMod K n).ker
  exact (ker_mod_range K E
    (FLExt.integerUnitNorm K E) hLocal hOrderNorm).symm

/-- The norm group of the bundled canonical unramified subextension consists
exactly of the elements whose normalized order is divisible by `n`. -/
theorem unramified_subextension_ker
    (n : ℕ) [NeZero n] :
    (canonicalUnramifiedSubextension K n).normGroup =
      (localOrderMod K n).ker :=
  unramified_level_ker K n

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Membership in the order-modulo-`n` kernel means exactly that the
normalized order is divisible by `n`. -/
theorem mod_ker_dvd
    (n : ℕ) [NeZero n] (x : Kˣ) :
    x ∈ (localOrderMod K n).ker ↔
      (n : ℤ) ∣ localUnitOrder K (Additive.ofMul x) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    exact congrArg Multiplicative.toAdd hx
  · intro hx
    apply Multiplicative.toAdd.injective
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hx

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The normalized-order kernel is open in the usual local-field topology. -/
theorem mod_ker_open
    (n : ℕ) [NeZero n] :
    IsOpen ((localOrderMod K n).ker : Set Kˣ) := by
  apply Subgroup.isOpen_mono
      (H₁ := localUnitSubgroup K)
      (H₂ := (localOrderMod K n).ker)
      _ (local_unit_open K)
  intro x hx
  apply (mod_ker_dvd K n x).2
  have hxval : valuation K (x : K) = 1 :=
    (local_subgroup K x).1 hx
  have hxorder : localUnitOrder K (Additive.ofMul x) = 0 := by
    apply le_antisymm
    · have h := (local_order_valuation K x 1).2
          (by simp [hxval])
      simpa using h
    · have h := (local_order_valuation K 1 x).2
          (by simp [hxval])
      simpa using h
  rw [hxorder]
  exact dvd_zero _

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The normalized-order kernel has finite index. -/
theorem local_mod_index
    (n : ℕ) [NeZero n] :
    (localOrderMod K n).ker.FiniteIndex := by
  infer_instance

/-- The order-congruence subgroup is unconditionally realized as a norm
group by the canonical unramified extension. -/
theorem local_mod_group
    (n : ℕ) [NeZero n] :
    LGroup K (localOrderMod K n).ker :=
  ⟨canonicalUnramifiedSubextension K n,
    unramified_subextension_ker K n⟩

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The canonical unramified norm groups satisfy both sides of the Local
Existence Theorem without assuming local reciprocity. -/
theorem mod_open_index
    (n : ℕ) [NeZero n] :
    OFSubgro (localOrderMod K n).ker :=
  ⟨mod_ker_open K n,
    local_mod_index K n⟩

end

end Towers.CField.LFTheory
