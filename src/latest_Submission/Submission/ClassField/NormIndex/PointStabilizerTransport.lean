import Submission.ClassField.NormIndex.FiniteOrbitReindexing

/-!
# Point-stabilizer transport for finite norm coordinates

This isolates the dependent completion-cast calculation used in the finite
idèle norm formula.  Keeping it in its own module lets downstream product
arguments use the checked equality without repeatedly normalizing its casts.
-/

namespace Submission.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

private theorem ring_cast_pi
    {I : Type*} {R : I → Type*}
    [∀ i, Mul (R i)] [∀ i, Add (R i)]
    (x : ∀ i, R i) {i j : I} (h : i = j) :
    RingEquiv.cast h (x i) = x j := by
  subst j
  rfl

set_option maxHeartbeats 600000 in
-- The source and target completion rings depend on equal prime indices, so
-- composing the two transports requires substantial proof reduction.
set_option maxRecDepth 100000 in
/-- Returning a centered stabilizer term to a chosen completion gives the
term indexed by the corresponding element of the global Galois group. -/
theorem transport_point_stabilizer
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    (x : ∀ Q : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Q.adicCompletion L) :
    letI := finitePrimeAction (K := K) (L := L)
    letI : MulAction.IsPretransitive Gal(L/K)
        (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
      completion_above_pretransitive P
    let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
    let qw := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    let q₀ := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w₀)
    let hreturn : qw = r⁻¹ • q₀ :=
      centered_return_smul (K := K) (L := L) P w₀ w
    let hfix : qw = h.1⁻¹ • qw :=
      centered_upper_stabilizer
        (K := K) (L := L) P w h
    finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn
          (finitePlaceTransport (K := K) h.1 qw
            (RingEquiv.cast hfix (x qw)))) =
      finitePlaceTransport (K := K) (r * h.1) q₀
        (x ((r * h.1)⁻¹ • q₀)) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
    completion_above_pretransitive P
  dsimp only
  let r := completionPlaceReturn (FinitePlace.mk P).val w₀ w
  let qw := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)
  let q₀ := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w₀)
  let hreturn : qw = r⁻¹ • q₀ :=
    centered_return_smul (K := K) (L := L) P w₀ w
  let hfix : qw = h.1⁻¹ • qw :=
    centered_upper_stabilizer
      (K := K) (L := L) P w h
  let hsource : qw = (r * h.1)⁻¹ • q₀ := by
    calc
      qw = h.1⁻¹ • qw := hfix
      _ = h.1⁻¹ • (r⁻¹ • q₀) :=
        congrArg (fun Q => h.1⁻¹ • Q) hreturn
      _ = (r * h.1)⁻¹ • q₀ := by
        rw [mul_inv_rev, mul_smul]
  have htransport := transport_return_stabilizer
    (K := K) (L := L) P w₀ w h x
  have hcast : RingEquiv.cast hsource (x qw) =
      x ((r * h.1)⁻¹ • q₀) :=
    ring_cast_pi x hsource
  calc
    _ = finitePlaceTransport (K := K) (r * h.1) q₀
          (RingEquiv.cast hsource (x qw)) := htransport
    _ = _ := congrArg
      (finitePlaceTransport (K := K) (r * h.1) q₀) hcast

end

end Submission.CField.NIndex
