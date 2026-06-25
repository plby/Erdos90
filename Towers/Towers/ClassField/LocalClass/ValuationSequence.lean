import Towers.ClassField.Shifting.CyclicTateShape
import Towers.ClassField.NormCorrespondence.SubgroupOpenClosed
import Towers.ClassField.LocalBrauer.FiniteExtensionOrder

/-!
# The valuation exact sequence for Lemma III.2.5

For a finite local Galois extension, normalized order is a surjective
Galois-equivariant map `Lˣ → ℤ`.  Its kernel is the natural representation
of local units.
-/

namespace Towers.CField.LClass

open CategoryTheory CategoryTheory.Limits
open Towers.CField.LFTheory
open Towers.CField.LBrauer

noncomputable section

attribute [local instance] Units.mulDistribMulActionRight

universe u

/-- A local-field unit has normalized additive order zero, and conversely. -/
theorem local_order_zero
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    (x : Fˣ) :
    x ∈ localUnitSubgroup F ↔
      localUnitOrder F (Additive.ofMul x) = 0 := by
  constructor
  · intro hx
    have hxval : ValuativeRel.valuation F (x : F) = 1 :=
      (local_subgroup F x).1 hx
    apply le_antisymm
    · have h := (local_order_valuation F x 1).2
          (by simp [hxval])
      simpa using h
    · have h := (local_order_valuation F 1 x).2
          (by simp [hxval])
      simpa using h
  · intro hx
    apply (local_subgroup F x).2
    apply le_antisymm
    · have hle : localUnitOrder F (Additive.ofMul (1 : Fˣ)) ≤
          localUnitOrder F (Additive.ofMul x) := by
        simp [hx]
      simpa using
        (local_order_valuation F (1 : Fˣ) x).1 hle
    · have hle : localUnitOrder F (Additive.ofMul x) ≤
          localUnitOrder F (Additive.ofMul (1 : Fˣ)) := by
        simp [hx]
      simpa using
        (local_order_valuation F x (1 : Fˣ)).1 hle

/-- The local-unit subgroup of the finite extension, formed using its
canonical spectral norm and valuation. -/
noncomputable def extensionUnitSubgroup
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    Subgroup Lˣ := by
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
  exact localUnitSubgroup L

/-- The natural Galois action on the local units. -/
@[implicit_reducible]
noncomputable def localDistribAction
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    MulDistribMulAction Gal(L/K) (extensionUnitSubgroup K L) := by
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
  exact
    { smul := fun g u ↦ ⟨g • (u : Lˣ), by
        apply (local_order_zero L _).2
        change localUnitOrder L
            (Additive.ofMul (Units.map g.toMonoidHom (u : Lˣ))) = 0
        rw [FLExt.unit_order_aut K L]
        apply (local_order_zero L _).1
        exact u.2⟩
      one_smul := fun u ↦ Subtype.ext (one_smul Gal(L/K) (u : Lˣ))
      mul_smul := fun g h u ↦ Subtype.ext (mul_smul g h (u : Lˣ))
      smul_mul := fun g u v ↦ Subtype.ext (smul_mul' g (u : Lˣ) (v : Lˣ))
      smul_one := fun g ↦ Subtype.ext (smul_one g) }

/-- The integral representation carried by the local units `U_L`. -/
noncomputable abbrev localUnitRepresentation
    (K L : Type u)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    Rep ℤ Gal(L/K) :=
  let _ := localDistribAction K L
  Rep.ofMulDistribMulAction Gal(L/K)
    (extensionUnitSubgroup K L)

/-- Normalized order as a morphism from the natural representation on
`Lˣ` to the trivial integral representation. -/
noncomputable def localRepHom
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    Rep.ofAlgebraAutOnUnits K L ⟶ Rep.trivial ℤ Gal(L/K) ℤ := by
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
  apply Rep.ofHom
  refine ⟨(localUnitOrder L).toIntLinearMap, ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  change localUnitOrder L
      (Additive.ofMul (Units.map g.toMonoidHom x.toMul)) =
    localUnitOrder L x
  exact FLExt.unit_order_aut K L g x.toMul

/-- Inclusion of local units into all nonzero elements. -/
noncomputable def inclusionRepHom
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    localUnitRepresentation K L ⟶ Rep.ofAlgebraAutOnUnits K L := by
  letI := localDistribAction K L
  apply Rep.ofHom
  let i : Additive (extensionUnitSubgroup K L) →+
      Additive Lˣ :=
    { toFun := fun u ↦ Additive.ofMul (u.toMul : Lˣ)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  refine ⟨i.toIntLinearMap, ?_⟩
  intro g
  apply LinearMap.ext
  intro u
  rfl

/-- The valuation sequence written with the actual local-unit subgroup. -/
noncomputable abbrev localShortComplex
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk (inclusionRepHom K L)
    (localRepHom K L) (by
      ext u
      change Additive (extensionUnitSubgroup K L) at u
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
      change localUnitOrder L (Additive.ofMul (u.toMul : Lˣ)) = 0
      exact (local_order_zero L _).1
        u.toMul.2)

/-- The local-unit inclusion realizes the kernel of normalized order. -/
noncomputable def localInclusionKernel
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    IsLimit (KernelFork.ofι (inclusionRepHom K L)
      (localShortComplex K L).zero) := by
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
  letI := localDistribAction K L
  letI : Mono (inclusionRepHom K L) :=
    (Rep.mono_iff_injective _).2 fun x y hxy ↦
      Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul hxy))
  apply KernelFork.IsLimit.ofι'
  intro A k hk
  letI : Module ℤ A := A.hV2
  letI : Module ℤ (localUnitRepresentation K L) :=
    (localUnitRepresentation K L).hV2
  let lAdd : A →+ Additive (extensionUnitSubgroup K L) :=
    { toFun := fun x ↦ Additive.ofMul
        ⟨(k.hom x).toMul, by
          apply (local_order_zero L _).2
          have heq := congrArg
            (fun q : A ⟶ Rep.trivial ℤ Gal(L/K) ℤ ↦ q.hom x) hk
          change localUnitOrder L (k.hom x) = 0 at heq
          exact heq⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg Additive.toMul (map_zero k.hom)
      map_add' := fun x y ↦ by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg Additive.toMul (map_add k.hom x y) }
  let lLin : A →ₗ[ℤ] (localUnitRepresentation K L) :=
    { toFun := fun x ↦ lAdd x
      map_add' := lAdd.map_add
      map_smul' := fun n x ↦ by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact congrArg Additive.toMul (k.hom.toLinearMap.map_smul n x) }
  let l : A ⟶ localUnitRepresentation K L := by
    refine Rep.ofHom (ρ := A.ρ)
      (σ := (localUnitRepresentation K L).ρ) ⟨lLin, ?_⟩
    intro g
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Additive.toMul
      (LinearMap.congr_fun (k.hom.2 g) x)
  refine ⟨l, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rfl

/-- The valuation sequence `1 → U_L → Lˣ → ℤ → 0` is short exact. -/
theorem local_short_exact
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    (localShortComplex K L).ShortExact := by
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
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _
      (localInclusionKernel K L)
  · rw [Rep.mono_iff_injective]
    intro x y hxy
    exact Additive.toMul.injective (Subtype.ext (congrArg Additive.toMul hxy))
  · rw [Rep.epi_iff_surjective]
    intro z
    obtain ⟨x, hx⟩ := local_order_surjective L z
    exact ⟨x, hx⟩

/-- The canonical short complex `U_L → Lˣ → ℤ`, with `U_L` represented as
the kernel of normalized order. -/
noncomputable def valuationShortComplex
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk (kernel.ι (localRepHom K L))
    (localRepHom K L) (kernel.condition _)

/-- The local valuation sequence is short exact. -/
theorem valuation_short_exact
    (K L : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L] :
    (valuationShortComplex K L).ShortExact := by
  let f := localRepHom K L
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)
  · dsimp [valuationShortComplex]
    infer_instance
  · dsimp [valuationShortComplex]
    rw [Rep.epi_iff_surjective]
    intro z
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
    obtain ⟨x, hx⟩ := local_order_surjective L z
    exact ⟨x, hx⟩

end

end Towers.CField.LClass
