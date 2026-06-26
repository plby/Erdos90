import Towers.NumberTheory.Completions.DualBaseChange
import Towers.NumberTheory.Completions.FractionRingLattice

/-!
# Recovering coordinate differents from semilocal completion

This file packages the last algebraic step of the completion argument.  The
completed trace-dual calculation is combined with the integral and fraction
product decompositions.  Once the image of the global inverse-different
lattice is identified coordinatewise, every extended global different is
the corresponding local different.
-/

namespace Towers.NumberTheory.Milne

open Module Submodule nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

variable {R S K L C F Q ι κ : Type u}
  [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S] [IsDedekindDomain S]
  [Field K] [Field L]
  [Algebra R S] [IsTorsionFree R S]
  [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L]
  [Algebra R L] [Algebra K L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
  [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra R C]
  [Field F] [Algebra C F] [IsFractionRing C F]
  [Algebra R F] [IsScalarTower R C F]
  [Algebra K F] [IsScalarTower R K F]
  [CommRing Q] [Algebra (C ⊗[R] S) Q]
  [Algebra C Q] [IsScalarTower C (C ⊗[R] S) Q]
  [Algebra F Q] [IsScalarTower C F Q]
  [IsLocalization
    (Algebra.algebraMapSubmonoid (C ⊗[R] S) C⁰) Q]
  [IsFractionRing (C ⊗[R] S) Q]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Finite ι] [Finite κ]

variable (B E : ι → Type u)
  [∀ i, CommRing (B i)] [∀ i, IsDedekindDomain (B i)]
  [∀ i, Field (E i)]
  [∀ i, Algebra C (B i)] [∀ i, IsTorsionFree C (B i)]
  [∀ i, Algebra (B i) (E i)] [∀ i, IsFractionRing (B i) (E i)]
  [∀ i, Algebra F (E i)] [∀ i, Algebra C (E i)]
  [∀ i, IsScalarTower C F (E i)]
  [∀ i, IsScalarTower C (B i) (E i)]
  [∀ i, Module.Free F (E i)] [∀ i, Module.Finite F (E i)]
  [∀ i, Algebra.IsSeparable F (E i)]
  [∀ i, IsIntegralClosure (B i) C (E i)]
  [IsFractionRing (∀ i, B i) (∀ i, E i)]

set_option synthInstance.maxHeartbeats 100000 in
-- The result combines two dependent product algebra structures and their restricted scalars.
set_option maxHeartbeats 1000000 in
/-- Recover every local different from the completed image of the global
inverse-different lattice.

The compatibility hypothesis `he` says that the chosen `F`-algebra product
decomposition is the fraction-ring extension of the integral decomposition.
The hypothesis `himage` is the coordinate description of the extended global
inverse different.  The completed trace-dual identity itself is supplied by
`form_dual_submodule`. -/
theorem extended_semilocal_dual
    (b : Basis κ R S)
    (e₀ : (C ⊗[R] S) ≃ₐ[C] (∀ i, B i))
    (eQ : Q ≃ₐ[F] (∀ i, E i))
    (he : eQ.restrictScalars C =
      fractionRingAlg (X := Q) B E e₀)
    (f : ∀ i,
      FractionalIdeal (nonZeroDivisors S) L →+*
        FractionalIdeal (nonZeroDivisors (B i)) (E i))
    (himage :
      let e := scalarFractionTensor
        (R := R) (S := S) (K := K) (L := L)
        (C := C) (F := F) (Q := Q)
      (Submodule.span C
          ((fun x : L => e ((1 : F) ⊗ₜ[K] x)) ''
            (Submodule.traceDual R K (1 : Submodule S L) : Set L))).map
          (eQ.toLinearEquiv.restrictScalars C).toLinearMap =
        Submodule.pi Set.univ
          (fun i ↦
            (((f i
                (((differentIdeal R S : Ideal S) :
                    FractionalIdeal (nonZeroDivisors S) L)⁻¹) :
                FractionalIdeal (nonZeroDivisors (B i)) (E i)) :
                  Submodule (B i) (E i)).restrictScalars C))) :
    ∀ i, f i
        ((differentIdeal R S : Ideal S) :
          FractionalIdeal (nonZeroDivisors S) L) =
      ((differentIdeal C (B i) : Ideal (B i)) :
        FractionalIdeal (nonZeroDivisors (B i)) (E i)) := by
  classical
  letI := Fintype.ofFinite ι
  let e := scalarFractionTensor
    (R := R) (S := S) (K := K) (L := L)
    (C := C) (F := F) (Q := Q)
  let N : Submodule C Q :=
    (1 : Submodule (C ⊗[R] S) Q).restrictScalars C
  let D : ι → FractionalIdeal (nonZeroDivisors S) L := fun _ =>
    ((differentIdeal R S : Ideal S) :
      FractionalIdeal (nonZeroDivisors S) L)
  have hN : N.map
        (eQ.toLinearEquiv.restrictScalars C).toLinearMap =
      Submodule.pi Set.univ
        (fun i ↦ (1 : Submodule (B i) (E i)).restrictScalars C) := by
    have hN₀ := restrict_scalars_fraction
      (X := Q) B E e₀
    rw [← he] at hN₀
    exact hN₀
  have hdualQ :
      (Algebra.traceForm F Q).dualSubmodule N =
        Submodule.span C
          ((fun x : L => e ((1 : F) ⊗ₜ[K] x)) ''
            (Submodule.traceDual R K (1 : Submodule S L) : Set L)) :=
    form_dual_submodule
      (R := R) (S := S) (K := K) (L := L)
      (C := C) (F := F) (Q := Q) b
  have hdual : ((Algebra.traceForm F Q).dualSubmodule N).map
        (eQ.toLinearEquiv.restrictScalars C).toLinearMap =
      Submodule.pi Set.univ
        (fun i ↦
          (((f i ((D i)⁻¹) :
              FractionalIdeal (nonZeroDivisors (B i)) (E i)) :
                Submodule (B i) (E i)).restrictScalars C)) := by
    rw [hdualQ]
    exact himage
  exact mapped_ideals_dual
    B E eQ N f D hN hdual

end

end Towers.NumberTheory.Milne
