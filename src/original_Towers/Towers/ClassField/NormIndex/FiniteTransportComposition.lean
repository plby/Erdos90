import Towers.ClassField.NormIndex.FiniteReturnTransport

/-!
# Composition of finite-place transports

The return transport from one completion place to a chosen place composes
with an element of the first place's stabilizer as multiplication in the
global Galois group.
-/

namespace Towers.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u v

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance finiteNormCompositionNontrivialFact
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Fact (FinitePlace.mk P).val.IsNontrivial :=
  ⟨absolute_value_nontrivial P⟩

local instance finiteNormCompositionCompletionUltrametric
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    IsUltrametricDist (FinitePlace.mk P).val.Completion :=
  placeUltrametricDist P

local instance finiteNormCompositionPretransitive
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :=
  completion_above_pretransitive P

/-- Dependent ring transports commute with replacing the target index.  Keeping
the family of transports abstract here prevents the kernel from unfolding the
large completion equivalences when this elementary cast identity is used. -/
private theorem ring_cast_family
    {I : Type v} {R : I → Type u}
    [∀ i, Mul (R i)] [∀ i, Add (R i)]
    (g : I → I) (F : ∀ i, R (g i) ≃+* R i)
    {a b : I} (hab : a = b) (ha : a = g a) (hb : a = g b)
    (x : R a) :
    RingEquiv.cast hab (F a (RingEquiv.cast ha x)) =
      F b (RingEquiv.cast hb x) := by
  subst b
  rfl

private theorem ring_cast_trans
    {I : Type v} {R : I → Type u}
    [∀ i, Mul (R i)] [∀ i, Add (R i)]
    {a b c : I} (hab : a = b) (hbc : b = c) (x : R a) :
    RingEquiv.cast (hab.trans hbc) x =
      RingEquiv.cast hbc (RingEquiv.cast hab x) := by
  subst b
  subst c
  rfl

omit [FiniteDimensional K L] in
/-- Pointwise multiplication for finite-place transport, with the equality of
the two dependent source indices made explicit. -/
private theorem place_transport_cast
    (sigma tau : Gal(L/K))
    (P : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    ∀ (hsource : (sigma * tau)⁻¹ • P = tau⁻¹ • (sigma⁻¹ • P))
      (x : ((sigma * tau)⁻¹ • P).adicCompletion L),
    finitePlaceTransport (K := K) (sigma * tau) P x =
      finitePlaceTransport (K := K) sigma P
        (finitePlaceTransport (K := K) tau (sigma⁻¹ • P)
          (RingEquiv.cast hsource x)) := by
  letI := finitePrimeAction (K := K) (L := L)
  intro hsource x
  cases hsource
  rw [place_transport_mul]
  rfl

/-- A return transport followed by a stabilizer transport is the transport
by their product, with the source coordinate read from the dependent family. -/
theorem transport_return_stabilizer
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w₀ w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (h : CompletionPlaceStabilizer (FinitePlace.mk P).val w)
    (x : ∀ Q : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Q.adicCompletion L) :
    letI := finitePrimeAction (K := K) (L := L)
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
          congrArg (fun q => h.1⁻¹ • q) hreturn
        _ = (r * h.1)⁻¹ • q₀ := by rw [mul_inv_rev, mul_smul]
    finitePlaceTransport (K := K) r q₀
        (RingEquiv.cast hreturn
          (finitePlaceTransport (K := K) h.1 qw
            (RingEquiv.cast hfix (x qw)))) =
      finitePlaceTransport (K := K) (r * h.1) q₀
        (RingEquiv.cast hsource (x qw)) := by
  letI := finitePrimeAction (K := K) (L := L)
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
        congrArg (fun q => h.1⁻¹ • q) hreturn
      _ = (r * h.1)⁻¹ • q₀ := by rw [mul_inv_rev, mul_smul]
  let hindex : (r * h.1)⁻¹ • q₀ = h.1⁻¹ • (r⁻¹ • q₀) := by
    rw [mul_inv_rev, mul_smul]
  let hsource' : qw = h.1⁻¹ • (r⁻¹ • q₀) := hsource.trans hindex
  have hinner :
      RingEquiv.cast hreturn
          (finitePlaceTransport (K := K) h.1 qw
            (RingEquiv.cast hfix (x qw))) =
        finitePlaceTransport (K := K) h.1 (r⁻¹ • q₀)
          (RingEquiv.cast hsource' (x qw)) :=
    ring_cast_family
      (R := fun Q : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
        Q.adicCompletion L)
      (g := fun Q => h.1⁻¹ • Q)
      (F := fun Q => finitePlaceTransport (K := K) h.1 Q)
      hreturn hfix hsource' (x qw)
  rw [place_transport_cast
    (K := K) (L := L) r h.1 q₀ hindex
    (RingEquiv.cast hsource (x qw))]
  rw [← ring_cast_trans hsource hindex (x qw)]
  rw [hinner]

end


end Towers.CField.NIndex
