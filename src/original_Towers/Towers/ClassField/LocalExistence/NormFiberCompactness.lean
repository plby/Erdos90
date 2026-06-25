import Towers.ClassField.LocalExistence.FiniteReciprocity

/-!
# Compact fibres of finite local-field norms

This file supplies the concrete compact-fibre input used in Step III.5.2.
For a finite Galois extension with its spectral local-field topology, the
kernel of the norm on field units is compact.  Consequently every nonempty
norm fibre is compact.  Elements of `localNormCore` give such nonempty fibres
over every finite abelian subextension.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.LBrauer

noncomputable section

universe u v

/-- The fibre of the norm on unit groups over a base-field unit. -/
def normUnitFiber (K : Type u) (L : Type v)
    [CommRing K] [Ring L] [Algebra K L] (a : Kˣ) : Set Lˣ :=
  {y | normOnUnits K L y = a}

/-- A nonempty homomorphism fibre is a translate of its kernel. -/
theorem fiber_translate_ker
    (K : Type u) (L : Type v)
    [CommRing K] [CommRing L] [Algebra K L]
    (a : Kˣ) (y₀ : Lˣ) (hy₀ : normOnUnits K L y₀ = a) :
    normUnitFiber K L a =
      (fun z : Lˣ ↦ z * y₀) '' ((normOnUnits K L).ker : Set Lˣ) := by
  ext y
  constructor
  · intro hy
    refine ⟨y * y₀⁻¹, ?_, ?_⟩
    · change normOnUnits K L (y * y₀⁻¹) = 1
      rw [map_mul, map_inv, hy, hy₀, mul_inv_cancel]
    · simp
  · rintro ⟨z, hz, rfl⟩
    change normOnUnits K L (z * y₀) = a
    rw [map_mul, hz, one_mul, hy₀]

/-- A nonempty fibre of a continuous group homomorphism is compact as soon
as its kernel is compact. -/
theorem fiber_compact_ker
    (K : Type u) (L : Type v)
    [CommRing K] [CommRing L] [Algebra K L]
    [TopologicalSpace L] [IsTopologicalGroup Lˣ]
    (a : Kˣ) (y₀ : Lˣ) (hy₀ : normOnUnits K L y₀ = a)
    (hker : IsCompact ((normOnUnits K L).ker : Set Lˣ)) :
    IsCompact (normUnitFiber K L a) := by
  rw [fiber_translate_ker K L a y₀ hy₀]
  exact hker.image (continuous_id.mul continuous_const)

/-- For a finite Galois extension of a nonarchimedean local field, equipped
with the spectral topology, the kernel of the norm on field units is compact.

The proof realizes it as the continuous image of the kernel of the norm on
the compact integer-unit group. -/
theorem units_ker_compact
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    letI : IsNonarchimedeanLocalField L :=
      FLExt.nonarchimedeanLocalField K L
    IsCompact ((normOnUnits K L).ker : Set Lˣ) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  let A := (Valuation.integer (ValuativeRel.valuation L))ˣ
  let f : A →* localUnitSubgroup K := compactUnitNorm K L
  let j : A → Lˣ := fun y ↦ (integerUnitLocal L y : Lˣ)
  have hf : Continuous f := continuous_compact_norm K L
  have hkerClosed : IsClosed (f.ker : Set A) := by
    change IsClosed (f ⁻¹' ({1} : Set (localUnitSubgroup K)))
    exact isClosed_singleton.preimage hf
  have hcompactUniv : IsCompact (Set.univ : Set A) := isCompact_univ
  have hkerCompact : IsCompact (f.ker : Set A) :=
    hcompactUniv.of_isClosed_subset hkerClosed (Set.subset_univ _)
  have hj : Continuous j :=
    continuous_subtype_val.comp (continuous_integer_local L)
  have hjker : j '' (f.ker : Set A) =
      ((normOnUnits K L).ker : Set Lˣ) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change normOnUnits K L (integerUnitLocal L z : Lˣ) = 1
      apply Units.ext
      change f z = 1 at hz
      exact congrArg
        (fun q : localUnitSubgroup K ↦ (((q : Kˣ) : K))) hz
    · intro hy
      have hyUnit : y ∈ localUnitSubgroup L := by
        apply (field_unit_subgroup K L y).mp
        change normOnUnits K L y ∈ localUnitSubgroup K
        rw [hy]
        exact (localUnitSubgroup K).one_mem
      let z : A := localInteger L ⟨y, hyUnit⟩
      refine ⟨z, ?_, ?_⟩
      · change compactUnitNorm K L z = 1
        apply Subtype.ext
        apply Units.ext
        exact congrArg Units.val hy
      · apply Units.ext
        rfl
  rw [← hjker]
  exact hkerCompact.image hj

/-- Every element of the common finite-abelian norm subgroup has a nonempty
norm fibre over each finite abelian subextension. -/
theorem norm_fiber_core
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
    (a : Kˣ) (ha : a ∈ localNormCore K)
    (L : FASubext K) :
    (normUnitFiber K L.1 a).Nonempty := by
  rw [localNormCore, familyCore, Subgroup.mem_iInf] at ha
  exact ha L

/-- Combining the preceding results, the full norm fibre over a norm-core
element is nonempty and compact in the spectral topology on the extension. -/
theorem fiber_compact_core
    (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (a : Kˣ) (ha : a ∈ localNormCore K)
    (L : FASubext K) :
    letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
    letI : NontriviallyNormedField L.1 :=
      FLExt.nontriviallyNormedField K L.1
    letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
    letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
    letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
    letI : IsNonarchimedeanLocalField L.1 :=
      FLExt.nonarchimedeanLocalField K L.1
    IsCompact (normUnitFiber K L.1 a) := by
  letI : Algebra.IsAlgebraic K L.1 := Algebra.IsAlgebraic.of_finite K L.1
  letI : NontriviallyNormedField L.1 :=
    FLExt.nontriviallyNormedField K L.1
  letI : NormedAlgebra K L.1 := spectralNorm.normedAlgebra K L.1
  letI : IsUltrametricDist L.1 := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L.1 := FLExt.valuativeRel K L.1
  letI : Valuation.Compatible (NormedField.valuation (K := L.1)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L.1))
  letI : IsNonarchimedeanLocalField L.1 :=
    FLExt.nonarchimedeanLocalField K L.1
  obtain ⟨y₀, hy₀⟩ := norm_fiber_core K a ha L
  exact fiber_compact_ker K L.1 a y₀ hy₀
    (units_ker_compact K L.1)

end

end Towers.CField.LExist
