import Towers.ClassField.Ideles.IdeleClassNorm
import Towers.ClassField.LocalReciprocity.FiniteIndexCore

/-! # Chapter VIII, Section 4, Theorem 4.8: Norm Limitation -/

namespace Towers.CField.GClass

open NumberField
open Towers.CField.Ideles

noncomputable section
universe u

/-- `M` is the largest intermediate field of `E/K` which is Galois and
abelian over `K`. -/
def MaximalGaloisSubextension
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    (M : IntermediateField K E) : Prop :=
  IsGalois K M ∧ IsMulCommutative Gal(M/K) ∧
    ∀ F : IntermediateField K E,
      IsGalois K F → IsMulCommutative Gal(F/K) → F ≤ M

/-- Norm transitivity gives the easy inclusion in the norm limitation
theorem. -/
def NormContainmentBridge : Prop :=
  ∀ (K E : Type u) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]
    (M : IntermediateField K E),
    (canonicalIdeleNorm (K := K) (L := E)).range ≤
      (canonicalIdeleNorm (K := K) (L := M)).range

/-- The fundamental-class/corestriction diagram identifies the two quotient
groups, hence the two norm subgroups have equal index. -/
def IndexBridge : Prop :=
  ∀ (K E : Type u) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]
    (M : IntermediateField K E),
    MaximalGaloisSubextension K E M →
    (canonicalIdeleNorm (K := K) (L := E)).range.FiniteIndex ∧
      (canonicalIdeleNorm (K := K) (L := M)).range.FiniteIndex ∧
      (canonicalIdeleNorm (K := K) (L := E)).range.index =
        (canonicalIdeleNorm (K := K) (L := M)).range.index

/-- **Theorem VIII.4.8 (Norm Limitation Theorem).** -/
def MaximalSubextensionEquality : Prop :=
  ∀ (K E : Type u) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]
    (M : IntermediateField K E),
    MaximalGaloisSubextension K E M →
    (canonicalIdeleNorm (K := K) (L := E)).range =
      (canonicalIdeleNorm (K := K) (L := M)).range

theorem containment_index
    (hcontain : NormContainmentBridge.{u})
    (hindex : IndexBridge.{u}) :
    MaximalSubextensionEquality.{u} := by
  intro K E _ _ _ _ _ _ M hmax
  obtain ⟨hfiniteE, hfiniteM, hindexEq⟩ := hindex K E M hmax
  letI : (canonicalIdeleNorm (K := K) (L := E)).range.FiniteIndex :=
    hfiniteE
  letI : (canonicalIdeleNorm (K := K) (L := M)).range.FiniteIndex :=
    hfiniteM
  exact Towers.CField.LRecip.subgroup_index
    (hcontain K E M) hindexEq

end
end Towers.CField.GClass
