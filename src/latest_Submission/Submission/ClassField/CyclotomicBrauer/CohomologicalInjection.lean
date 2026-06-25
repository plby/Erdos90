import Submission.ClassField.CyclotomicBrauer.LocalizationStatements
import Submission.ClassField.IdeleCohomology.RestrictedProductAction
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Chapter VII, Theorem 7.1: the finite cohomological injection

For the short exact sequence

`0 → Lˣ → I_L → C_L → 0`,

Milne uses `H¹(G,C_L) = 0` and the long exact sequence to inject
`H²(G,Lˣ)` into `H²(G,I_L)`.  This file proves that step for an arbitrary
short exact sequence of representations.  The arithmetic specialization only
has to supply the three representations and the idele-cohomology direct-sum
identification.
-/

namespace Submission.CField.CBrauer

open CategoryTheory CategoryTheory.Limits groupCohomology
open Submission.CField.BGroups
open Submission.CField.Ideles
open Submission.CField.ICohomo

universe u v w

variable {k G : Type u} [CommRing k] [Group G]

noncomputable section

/-- **Theorem VII.7.1, finite cohomological step.** In a short exact
sequence `0 → A → B → C → 0`, vanishing of `H¹(G,C)` makes the induced
map `H²(G,A) → H²(G,B)` injective. -/
theorem h_1_third
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hH1 : IsZero (H1 X.X₃)) :
    Function.Injective
      (groupCohomology.map (MonoidHom.id G) X.f 2) := by
  let S := mapShortComplex₁ hX (i := 1) (j := 2) rfl
  have hS : S.Exact := mapShortComplex₁_exact hX rfl
  have hzero : S.f = 0 := hH1.eq_of_src S.f 0
  letI : Mono S.g := hS.mono_g hzero
  exact (ModuleCat.mono_iff_injective S.g).mp inferInstance

/-- After identifying the middle `H²` with a direct sum of local groups, the
resulting localization map is still injective. -/
theorem h_localization_third
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hH1 : IsZero (H1 X.X₃))
    {D : Type u} [AddCommGroup D]
    (localDecomposition : H2 X.X₂ ≃+ D) :
    Function.Injective (fun x : H2 X.X₁ ↦
      localDecomposition
        (groupCohomology.map (MonoidHom.id G) X.f 2 x)) :=
  localDecomposition.injective.comp
    (h_1_third hX hH1)

/-- The cohomological bridge to Theorem VII.7.1.  If the global class group is
identified with `H²(G,A)`, the middle cohomology with the local direct sum, and
localization is the map induced by `A ⟶ B`, then localization is injective. -/
theorem brauer_injectivity_cohomological
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hH1 : IsZero (H1 X.X₃))
    {index : Type w} {Global : Type v} {Local : index → Type v}
    [CommGroup Global] [∀ v, CommGroup (Local v)]
    (loc : MultiplicativeLocalizationData Global Local)
    (globalComparison : Additive Global ≃+ H2 X.X₁)
    (localDecomposition : H2 X.X₂ ≃+
      DirectSum index (fun v ↦ Additive (Local v)))
    (hcompat : ∀ x : Additive Global,
      loc.localization x = localDecomposition
        (groupCohomology.map (MonoidHom.id G) X.f 2
          (globalComparison x))) :
    BrauerLocalizationInjectivity loc := by
  intro x y hxy
  apply globalComparison.injective
  apply h_1_third hX hH1
  apply localDecomposition.injective
  rw [← hcompat x, ← hcompat y]
  exact hxy

/-- The actual relative-Brauer specialization of the cohomological bridge.
The remaining arithmetic work is precisely to construct the two comparison
isomorphisms and prove `hcompat` for completion scalar extension. -/
theorem relative_injectivity_cohomological
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hH1 : IsZero (H1 X.X₃))
    {index K L : Type u}
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (Kv Lv : index → Type u)
    [∀ v, Field (Kv v)] [∀ v, Field (Lv v)]
    [∀ v, Algebra (Kv v) (Lv v)] [∀ v, IsGalois (Kv v) (Lv v)]
    (loc : MultiplicativeLocalizationData
      (relativeBrauerGroup K L)
      (fun v ↦ relativeBrauerGroup (Kv v) (Lv v)))
    (globalComparison : Additive (relativeBrauerGroup K L) ≃+ H2 X.X₁)
    (localDecomposition : H2 X.X₂ ≃+
      DirectSum index
        (fun v ↦ Additive (relativeBrauerGroup (Kv v) (Lv v))))
    (hcompat : ∀ x : Additive (relativeBrauerGroup K L),
      loc.localization x = localDecomposition
        (groupCohomology.map (MonoidHom.id G) X.f 2
          (globalComparison x))) :
    RelativeLocalizationInjectivity Kv Lv loc := by
  change BrauerLocalizationInjectivity loc
  exact brauer_injectivity_cohomological hX hH1 loc
    globalComparison localDecomposition hcompat

/-- The complete arithmetic input used in Milne's proof of Theorem VII.7.1.

The first representation is the multiplicative Galois module `Lˣ`; the
second is the idele module `I_L`; and the third is the idele-class module
`C_L`.  Keeping the two arrows in the structure makes the exact sequence and
the comparison with completion scalar extension part of the statement,
rather than leaving them implicit in a choice of abstract representations. -/
structure RelativeCohomologicalData
    {index K L : Type}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L]
    (Kv Lv : index → Type)
    [∀ v, Field (Kv v)] [∀ v, Field (Lv v)]
    [∀ v, Algebra K (Kv v)]
    [∀ v, Algebra (Kv v) (Lv v)] [∀ v, IsGalois (Kv v) (Lv v)]
    (loc : RelativeLocalizationData (K := K) (L := L) Kv Lv) where
  /-- The actual Galois action on `I_L`, including its coordinate formula. -/
  ideleAction : IAData (K := K) (L := L)
  /-- The quotient representation carried by the idele class group of `L`. -/
  ideleClassRep : Rep ℤ Gal(L/K)
  /-- The underlying multiplicative group really is `C_L = I_L / Lˣ`. -/
  ideleClassComparison : Multiplicative ideleClassRep ≃*
    IdeleClassGroup (NumberField.RingOfIntegers L) L
  /-- The equivariant quotient map `I_L → C_L`. -/
  toIdeleClass : ideleAction.representation ⟶ ideleClassRep
  idele_class_quotient :
    ∀ x : IdeleGroup (NumberField.RingOfIntegers L) L,
      ideleClassComparison
          (Multiplicative.ofAdd (toIdeleClass (Additive.ofMul x))) =
        QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers L) L) x
  principal_comp_quotient :
    ideleAction.principalIdeleHom ≫ toIdeleClass = 0
  shortExact :
    (ShortComplex.mk ideleAction.principalIdeleHom toIdeleClass
      principal_comp_quotient).ShortExact
  /-- The second-inequality input `H¹(G, C_L) = 0`. -/
  idele1Zero : IsZero (H1 ideleClassRep)
  /-- The crossed-product identification
  `Br(L/K) ≃ H²(G, Lˣ)`. -/
  globalComparison :
    Additive (relativeBrauerGroup K L) ≃+
      H2 (Rep.ofAlgebraAutOnUnits K L)
  /-- Proposition VII.2.5(b), followed by the local crossed-product
  identifications. -/
  localDecomposition : H2 ideleAction.representation ≃+
    DirectSum index
      (fun v ↦ Additive (relativeBrauerGroup (Kv v) (Lv v)))
  /-- The localization square: scalar extension to every completion agrees
  with the map on `H²` induced by the principal-idele embedding. -/
  localizationCompatibility :
    ∀ x : Additive (relativeBrauerGroup K L),
      loc.multiplicativeLocalizationData.localization x = localDecomposition
        (groupCohomology.map (MonoidHom.id Gal(L/K))
          ideleAction.principalIdeleHom 2
          (globalComparison x))

/-- **Theorem VII.7.1, arithmetic reduction.** Once the actual idele and
idele-class representations satisfy the precise data above, relative Brauer
localization is injective. -/
theorem relative_localization_injectivity
    {index K L : Type}
    [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L]
    (Kv Lv : index → Type)
    [∀ v, Field (Kv v)] [∀ v, Field (Lv v)]
    [∀ v, Algebra K (Kv v)]
    [∀ v, Algebra (Kv v) (Lv v)] [∀ v, IsGalois (Kv v) (Lv v)]
    (loc : RelativeLocalizationData (K := K) (L := L) Kv Lv)
    (data : RelativeCohomologicalData Kv Lv loc) :
    ArithmeticLocalizationInjectivity Kv Lv loc := by
  change BrauerLocalizationInjectivity loc.multiplicativeLocalizationData
  intro x y hxy
  apply data.globalComparison.injective
  apply h_1_third
    data.shortExact data.idele1Zero
  apply data.localDecomposition.injective
  rw [← data.localizationCompatibility x,
    ← data.localizationCompatibility y]
  exact hxy

end

end Submission.CField.CBrauer
