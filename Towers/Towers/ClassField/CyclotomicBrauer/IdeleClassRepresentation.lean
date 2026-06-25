import Towers.ClassField.CyclotomicBrauer.CohomologicalInjection
import Towers.ClassField.IdeleCohomology.CompletionInducedModule

/-!
# Chapter VII, Theorem 7.1

This file gives the finite-extension proof of Milne's global-to-local
injection in degree two.  The idele class representation is constructed as
the cokernel of the diagonal map `Lˣ → I_L`; consequently the short exact
sequence used in the proof is not an additional hypothesis.

The two inputs are exactly the earlier results cited by Milne:

* Theorem VII.5.1: `H¹(G, C_L) = 0`;
* Proposition VII.2.5(b): `H²(G, I_L)` is the direct sum of the local
  groups `H²(Gᵛ, Lᵛˣ)`.
-/

namespace Towers.CField.CBrauer

open CategoryTheory CategoryTheory.Limits groupCohomology
open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

variable {K L : Type} [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The idele-class representation attached to an actual Galois action on
the ideles: categorically it is the quotient of `I_L` by the diagonal copy
of `Lˣ`. -/
abbrev classCokernelRepresentation
    (D : IAData (K := K) (L := L)) : Rep ℤ Gal(L/K) :=
  cokernel D.principalIdeleHom

/-- The canonical complex `0 → Lˣ → I_L → C_L → 0`. -/
def cokernelShortComplex
    (D : IAData (K := K) (L := L)) :
    ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk D.principalIdeleHom (cokernel.π D.principalIdeleHom)
    (cokernel.condition D.principalIdeleHom)

/-- The diagonal map from global units to ideles is a monomorphism. -/
instance principal_idele_mono
    (D : IAData (K := K) (L := L)) :
    Mono D.principalIdeleHom := by
  apply (Rep.mono_iff_injective D.principalIdeleHom).2
  intro x y hxy
  apply Additive.toMul.injective
  apply principalIdele_injective (NumberField.RingOfIntegers L) L
  exact congrArg Additive.toMul hxy

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] in
/-- The categorical cokernel realizes the usual short exact idele-class
sequence. -/
theorem cokernelShortExact
    (D : IAData (K := K) (L := L)) :
    (cokernelShortComplex D).ShortExact := by
  apply ShortComplex.ShortExact.mk'
      (ShortComplex.exact_cokernel D.principalIdeleHom)
  · change Mono D.principalIdeleHom
    infer_instance
  · infer_instance

/-- The absolute value represented by a finite or infinite number-field
place. -/
def numberAbsoluteValue
    (v : NumberFieldPlace K) : AbsoluteValue K ℝ :=
  match v with
  | .inl v => (FinitePlace.mk v).val
  | .inr v => v.1

/-- A choice of one prolongation `w | v` at every place gives the direct sum
of the local degree-two cohomology groups occurring in Theorem VII.7.1. -/
abbrev HDirectSum
    (w : ∀ v : NumberFieldPlace K,
      CompletionPlacesAbove (L := L) (numberAbsoluteValue v)) :=
  DirectSum (NumberFieldPlace K) (fun v ↦
    H2 (placeUnitsRepresentation
      (numberAbsoluteValue v) (w v)))

/-- The canonical finite global-to-local map, expressed as the map induced
by `Lˣ → I_L`, followed by Proposition VII.2.5(b)'s local decomposition. -/
def globalH2
    (D : IAData (K := K) (L := L))
    (w : ∀ v : NumberFieldPlace K,
      CompletionPlacesAbove (L := L) (numberAbsoluteValue v))
    (localDecomposition : H2 D.representation ≃+
      HDirectSum (K := K) (L := L) w) :
    H2 (Rep.ofAlgebraAutOnUnits K L) →+
      HDirectSum (K := K) (L := L) w :=
  localDecomposition.toAddMonoidHom.comp
    (groupCohomology.map (MonoidHom.id Gal(L/K))
      D.principalIdeleHom 2).hom.toAddMonoidHom

omit [FiniteDimensional K L] [IsGalois K L] in
/-- **Theorem VII.7.1, finite case.**  The canonical map

`H²(L/K) → ⊕ v, H²(Lᵛ/K_v)`

is injective.  Its two hypotheses are the named earlier theorems used in
Milne's proof, now stated against the actual idele and completion
representations. -/
theorem ideleCokernelRepresentation
    (D : IAData (K := K) (L := L))
    (w : ∀ v : NumberFieldPlace K,
      CompletionPlacesAbove (L := L) (numberAbsoluteValue v))
    (hH1 : IsZero (H1 (classCokernelRepresentation D)))
    (localDecomposition : H2 D.representation ≃+
      HDirectSum (K := K) (L := L) w) :
    Function.Injective
      (globalH2 D w localDecomposition) := by
  simpa only [globalH2, AddMonoidHom.coe_comp,
    Function.comp_apply, cokernelShortComplex] using
    (h_localization_third
      (cokernelShortExact D) hH1 localDecomposition)

end

end Towers.CField.CBrauer
