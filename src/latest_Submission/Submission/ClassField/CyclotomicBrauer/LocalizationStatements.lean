import Submission.ClassField.BrauerGroups.BaseChangeBrauer
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.Galois.Basic

/-!
# The Brauer localization map

The canonical localization map has finite support, so it lands in a direct
sum rather than the unrestricted product.  `MultiplicativeLocalizationData`
keeps both the coordinate maps and that direct-sum lift visible.  Later files
can therefore state injectivity and exactness without assuming finite support
silently.
-/

namespace Submission.CField.CBrauer

open Submission.CField.BGroups

noncomputable section

universe u v w

/-- A family of multiplicative localization maps together with its
finite-support lift to the additive direct sum. -/
structure MultiplicativeLocalizationData
    {index : Type u} (Global : Type v) (Local : index → Type w)
    [CommGroup Global] [∀ v, CommGroup (Local v)] where
  localizeAt : ∀ v, Global →* Local v
  localization : Additive Global →+
    DirectSum index (fun v ↦ Additive (Local v))
  localization_apply : ∀ (x : Global) (v : index),
    DirectSum.component ℤ index (fun v ↦ Additive (Local v)) v
        (localization (Additive.ofMul x)) =
      Additive.ofMul (localizeAt v x)

/-- The arithmetic localization data for a relative Brauer group.  Besides
the finite-support lift, this records that every coordinate is genuinely
scalar extension from `K` to the corresponding completion `Kv v`. -/
structure RelativeLocalizationData
    {index K L : Type u}
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (Kv Lv : index → Type u)
    [∀ v, Field (Kv v)] [∀ v, Field (Lv v)]
    [∀ v, Algebra K (Kv v)]
    [∀ v, Algebra (Kv v) (Lv v)] [∀ v, IsGalois (Kv v) (Lv v)] where
  multiplicativeLocalizationData : MultiplicativeLocalizationData
    (relativeBrauerGroup K L)
    (fun v ↦ relativeBrauerGroup (Kv v) (Lv v))
  localizeAt_coe : ∀ (x : relativeBrauerGroup K L) (v : index),
    ((multiplicativeLocalizationData.localizeAt v x :
        relativeBrauerGroup (Kv v) (Lv v)) : BrauerGroup (Kv v)) =
      brauerBaseChange K (Kv v) (x : BrauerGroup K)

/-- **Theorem VII.7.1.** The canonical map from a relative Brauer group to
the direct sum of the relative Brauer groups of the completions is injective.

For a possibly infinite Galois extension, `Local v` is formed after choosing
a prolongation above `v`; the theorem is independent of that choice. -/
def BrauerLocalizationInjectivity
    {index : Type u} {Global : Type v} {Local : index → Type w}
    [CommGroup Global] [∀ v, CommGroup (Local v)]
    (loc : MultiplicativeLocalizationData Global Local) : Prop :=
  Function.Injective loc.localization

/-- The actual relative-Brauer specialization of Theorem VII.7.1.  Supplying
`loc` includes the prolongations, scalar-extension maps, and their finite
support theorem. -/
def RelativeLocalizationInjectivity
    {index : Type u} {K L : Type v}
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (Kv Lv : index → Type v)
    [∀ v, Field (Kv v)] [∀ v, Field (Lv v)]
    [∀ v, Algebra (Kv v) (Lv v)] [∀ v, IsGalois (Kv v) (Lv v)]
    (loc : MultiplicativeLocalizationData
      (relativeBrauerGroup K L)
      (fun v ↦ relativeBrauerGroup (Kv v) (Lv v))) : Prop :=
  BrauerLocalizationInjectivity loc

/-- **Theorem VII.7.1, exact arithmetic statement.** The direct-sum map
whose coordinates are completion scalar extension is injective. -/
def ArithmeticLocalizationInjectivity
    {index K L : Type u}
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (Kv Lv : index → Type u)
    [∀ v, Field (Kv v)] [∀ v, Field (Lv v)]
    [∀ v, Algebra K (Kv v)]
    [∀ v, Algebra (Kv v) (Lv v)] [∀ v, IsGalois (Kv v) (Lv v)]
    (loc : RelativeLocalizationData (K := K) (L := L) Kv Lv) : Prop :=
  BrauerLocalizationInjectivity loc.multiplicativeLocalizationData

end

end Submission.CField.CBrauer
