import Towers.ClassField.GlobalClass.Corestriction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The corestriction square for Theorem VIII.4.8

Milne does not assume the final cokernel isomorphism in the norm-limitation
proof.  He obtains it from a commutative square whose horizontal arrows are
the fundamental-class Tate isomorphisms and whose vertical arrows are
corestriction.  This file formalizes the group-theoretic passage from that
literal square to the cokernel bridge used in the rest of the proof.
-/

namespace Towers.CField.GClass

open NumberField
open Towers.CField.LRecip
open Towers.CField.Ideles
open Towers.CField.NIndex

noncomputable section

universe u v w x

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- An isomorphism of commutative squares induces an isomorphism of the
two cokernels. -/
noncomputable def cokernelCommSquare
    {A : Type u} {B : Type v} {X : Type w} {Y : Type x}
    [Group A] [CommGroup B] [Group X] [CommGroup Y]
    (f : A →* B) (g : X →* Y)
    (eA : A ≃* X) (eB : B ≃* Y)
    (commutes : ∀ a, eB (f a) = g (eA a)) :
    (B ⧸ f.range) ≃* (Y ⧸ g.range) := by
  apply QuotientGroup.congr f.range g.range eB
  ext y
  constructor
  · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
    exact ⟨eA a, (commutes a).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨a, rfl⟩ := eA.surjective z
    exact ⟨f a, ⟨a, rfl⟩, commutes a⟩

/-- The norm `C_{Lᴴ} → C_K`, descended modulo the norm from `L` on
both sides.  This is the right vertical map in Milne's second diagram. -/
noncomputable def fixedModuloGalois
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    (CK E ⧸ (canonicalIdeleNorm (K := E) (L := L)).range) →*
      (CK K ⧸ (canonicalIdeleNorm (K := K) (L := L)).range) := by
  let E := IntermediateField.fixedField H
  letI : Algebra E L := E.val.toAlgebra
  letI : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  let normEL := canonicalIdeleNorm (K := E) (L := L)
  let normKE := canonicalIdeleNorm (K := K) (L := E)
  let normKL := canonicalIdeleNorm (K := K) (L := L)
  apply QuotientGroup.map normEL.range normKL.range normKE
  rintro _ ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  have htrans : normKL = normKE.comp normEL :=
    canonical_idele_trans
      (norm_trans_arbitrary (K := K) (E := E) (L := L))
  exact DFunLike.congr_fun htrans c

@[simp]
theorem fixed_modulo_mk
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K))
    (c : CK (IntermediateField.fixedField H)) :
    fixedModuloGalois K L H
        (QuotientGroup.mk'
          (canonicalIdeleNorm
            (K := IntermediateField.fixedField H) (L := L)).range c) =
      QuotientGroup.mk'
        (canonicalIdeleNorm (K := K) (L := L)).range
        (canonicalIdeleNorm
          (K := K) (L := IntermediateField.fixedField H) c) := by
  rfl

/-- The norm from `L` to `K` factors through the norm from the fixed field
`Lᴴ`, so its range is contained in the latter norm range. -/
theorem galois_range_fixed
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    (canonicalIdeleNorm (K := K) (L := L)).range ≤
      (canonicalIdeleNorm (K := K) (L := E)).range := by
  let E := IntermediateField.fixedField H
  letI : Algebra E L := E.val.toAlgebra
  letI : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  let normEL := canonicalIdeleNorm (K := E) (L := L)
  let normKE := canonicalIdeleNorm (K := K) (L := E)
  let normKL := canonicalIdeleNorm (K := K) (L := L)
  have htrans : normKL = normKE.comp normEL :=
    canonical_idele_trans
      (norm_trans_arbitrary (K := K) (E := E) (L := L))
  change normKL.range ≤ normKE.range
  intro x hx
  obtain ⟨c, hc⟩ := hx
  refine ⟨normEL c, ?_⟩
  calc
    normKE (normEL c) = normKL c :=
      (DFunLike.congr_fun htrans c).symm
    _ = x := hc

/-- The range of the descended fixed-field norm is the fixed-field norm
subgroup modulo the norm subgroup from `L`. -/
theorem fixed_modulo_range
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    (fixedModuloGalois K L H).range =
      (canonicalIdeleNorm (K := K) (L := E)).range.map
        (QuotientGroup.mk'
          (canonicalIdeleNorm (K := K) (L := L)).range) := by
  let E := IntermediateField.fixedField H
  letI : Algebra E L := E.val.toAlgebra
  letI : IsScalarTower K E L :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : FiniteDimensional E L := FiniteDimensional.right K E L
  let normEL := canonicalIdeleNorm (K := E) (L := L)
  let normKE := canonicalIdeleNorm (K := K) (L := E)
  let normKL := canonicalIdeleNorm (K := K) (L := L)
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective normEL.range z
    refine ⟨normKE c, ⟨c, rfl⟩, ?_⟩
    exact (fixed_modulo_mk K L H c).symm
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨QuotientGroup.mk' normEL.range c,
      fixed_modulo_mk K L H c⟩

/-- The cokernel of the right vertical norm map is the literal quotient
`C_K / Nm_{Lᴴ/K}(C_{Lᴴ})`, by Noether's third isomorphism theorem. -/
noncomputable def fixedCokernelEquiv
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    let E := IntermediateField.fixedField H
    ((CK K ⧸ (canonicalIdeleNorm (K := K) (L := L)).range) ⧸
        (fixedModuloGalois K L H).range) ≃*
      (CK K ⧸
        (canonicalIdeleNorm (K := K) (L := E)).range) := by
  let E := IntermediateField.fixedField H
  let NL := (canonicalIdeleNorm (K := K) (L := L)).range
  let NE := (canonicalIdeleNorm (K := K) (L := E)).range
  have hle : NL ≤ NE := galois_range_fixed K L H
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (fixed_modulo_range K L H)).trans
      (QuotientGroup.quotientQuotientEquivQuotient NL NE hle)

/-- The literal cohomological input in Milne's proof: the two
fundamental-class Tate isomorphisms and commutativity with corestriction.
Unlike `CorestrictionCokernelBridge`, this contains no cokernel or
norm-limitation conclusion. -/
def CorestrictionSquareBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)),
    let E := IntermediateField.fixedField H
    ∃ eH : Abelianization H ≃*
        (CK E ⧸ (canonicalIdeleNorm (K := E) (L := L)).range),
    ∃ eG : Abelianization Gal(L/K) ≃*
        (CK K ⧸ (canonicalIdeleNorm (K := K) (L := L)).range),
      ∀ h : Abelianization H,
        eG (abelianizedSubgroupInclusion H h) =
          fixedModuloGalois K L H (eH h)

/-- The commutative fundamental-class square implies the cokernel bridge
used by the fixed-field norm-limitation argument. -/
theorem corestriction_cokernel_square
    (hsquare : CorestrictionSquareBridge.{u}) :
    CorestrictionCokernelBridge.{u} := by
  intro K L _ _ _ _ _ _ _ H
  obtain ⟨eH, eG, hcomm⟩ := hsquare K L H
  let rightMap := fixedModuloGalois K L H
  let eCoker := cokernelCommSquare
    (abelianizedSubgroupInclusion H) rightMap eH eG hcomm
  exact ⟨(fixedCokernelEquiv K L H).symm.trans
    eCoker.symm⟩

end

end Towers.CField.GClass
