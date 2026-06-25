import Submission.ClassField.NormIndex.FiniteCanonicalTransitivity

/-!
# Finite norm coordinates indexed by literal upper primes

The Chapter V idèle norm indexes upper primes by factors of the extended
ideal.  Tower reindexing is cleaner with literal height-one primes, so this
file transports one completed norm to that equivalent index type.
-/

namespace Submission.CField.NIndex

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Reindex one value of a dependent family without constructing the full
dependent-function equivalence.  Keeping this transport opaque prevents the
large completion types below from being duplicated during type checking. -/
private def reindexDependent {α β : Type*} (P : β → Sort*) (e : α ≃ β)
    (f : (a : α) → P (e a)) (b : β) : P b :=
  e.apply_symm_apply b ▸ f (e.symm b)

private theorem reindexDependent_apply {α β : Type*} (P : β → Sort*)
    (e : α ≃ β) (f : (a : α) → P (e a)) (a : α) :
    reindexDependent P e f (e a) = f a := by
  change Equiv.piCongrLeft P e f (e a) = f a
  exact Equiv.piCongrLeft_apply_apply P e f a

/-- Unit-valued form of norm transport.  Proving this once over abstract rings
keeps the much larger prime-adic completion structures out of the proof term. -/
private theorem units_norm_equiv
    {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [Ring B₁]
    [CommRing A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂]
    (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) e₁.toRingHom =
      RingHom.comp e₂.toRingHom (algebraMap A₁ B₁)) (z : B₁ˣ) :
    Units.map e₁.toRingHom.toMonoidHom (Units.map (Algebra.norm A₁) z) =
      Units.map (Algebra.norm A₂)
        (Units.map e₂.toRingHom.toMonoidHom z) := by
  apply Units.ext
  change e₁ (Algebra.norm A₁ (z : B₁)) =
    Algebra.norm A₂ (e₂ (z : B₁))
  rw [Algebra.norm_eq_of_equiv_equiv e₁ e₂ he,
    RingEquiv.apply_symm_apply]

private def mapUnits {M N : Type*} [Monoid M] [Monoid N]
    (f : M →* N) : Mˣ →* Nˣ :=
  Units.map f

/-- The completed local norm indexed by a literal upper height-one prime. -/
noncomputable def completionNormLiteral
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K)) (Q : PlacesAbovePrime K L P) :
    (Q.1.adicCompletion L)ˣ →* (P.adicCompletion K)ˣ :=
  reindexDependent
    (fun R : PlacesAbovePrime K L P ↦
      (R.1.adicCompletion L)ˣ →* (P.adicCompletion K)ˣ)
    (upperPlacesAbove (K := K) (L := L) P)
    (fun q ↦ finiteCompletionNorm (K := K) (L := L) P q) Q

set_option maxHeartbeats 1000000 in
-- The inverse equivalence and completion cast normalize only after the
-- literal-prime equality is exposed.
set_option maxRecDepth 100000 in
/-- On the literal prime represented by a factor, the transported norm is
the original factor-indexed completed norm. -/
theorem completion_literal_equiv
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (q : UpperPrimeFactors (K := K) (L := L) P)
    (z : ((upperPrime (K := K) (L := L) P q).adicCompletion L)ˣ) :
    completionNormLiteral (K := K) (L := L) P
        (upperPlacesAbove
          (K := K) (L := L) P q) z =
      finiteCompletionNorm (K := K) (L := L) P q z := by
  exact DFunLike.congr_fun (reindexDependent_apply
    (fun R : PlacesAbovePrime K L P ↦
      (R.1.adicCompletion L)ˣ →* (P.adicCompletion K)ˣ)
    (upperPlacesAbove (K := K) (L := L) P)
    (fun q ↦ finiteCompletionNorm (K := K) (L := L) P q) q) z

/-- The finite norm coordinate, reindexed by literal upper primes. -/
theorem idele_norm_literal
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (x : FiniteIdeles (OK L) L) :
    finiteNorm (K := K) (L := L) P x =
      ∏ Q : PlacesAbovePrime K L P,
        completionNormLiteral (K := K) (L := L) P Q (x.1 Q.1) := by
  let e := upperPlacesAbove
    (K := K) (L := L) P
  change (∏ q : UpperPrimeFactors (K := K) (L := L) P,
      finiteCompletionNorm (K := K) (L := L) P q
        (x.1 (upperPrime (K := K) (L := L) P q))) = _
  calc
    _ = ∏ q : UpperPrimeFactors (K := K) (L := L) P,
        completionNormLiteral (K := K) (L := L) P (e q)
          (x.1 (e q).1) := by
      apply Finset.prod_congr rfl
      intro q _
      exact (completion_literal_equiv P q
        (x.1 (upperPrime (K := K) (L := L) P q))).symm
    _ = _ := e.prod_comp (fun Q ↦
      completionNormLiteral (K := K) (L := L) P Q (x.1 Q.1))

set_option maxRecDepth 100000 in
private theorem completion_norm_canonical
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (q : UpperPrimeFactors (K := K) (L := L) P)
    (z : ((upperPrime (K := K) (L := L) P q).adicCompletion L)ˣ) :
    finiteCompletionNorm (K := K) (L := L) P q z =
      mapUnits ((RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K)
        (upperPrime_under (K := K) (L := L) P q)).toRingHom.toMonoidHom)
        (finiteCanonicalNorm (K := K) (L := L)
          (upperPrime (K := K) (L := L) P q) z) := by
  let R := upperPrime (K := K) (L := L) P q
  let hRP : R.under (OK K) = P := upperPrime_under (K := K) (L := L) P q
  let hP : P.asIdeal.map (algebraMap (OK K) (OK L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra ((R.under (OK K)).adicCompletion K) (R.adicCompletion L) :=
    (coordinateExtensionHom (K := K) (L := L) R).toAlgebra
  letI : Algebra (P.adicCompletion K) (R.adicCompletion L) :=
    adicFactorAlgebra (K := K) (L := L) P hP q
  exact (units_norm_equiv
    (RingEquiv.cast
      (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K) hRP)
    (RingEquiv.refl (R.adicCompletion L))
    (extension_comp_cast P q) z).symm

private theorem completion_literal_canonical
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K)) (Q : PlacesAbovePrime K L P)
    (z : (Q.1.adicCompletion L)ˣ) :
    completionNormLiteral (K := K) (L := L) P Q z =
      mapUnits ((RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K)
        Q.2).toRingHom.toMonoidHom)
        (finiteCanonicalNorm (K := K) (L := L) Q.1 z) := by
  let e := upperPlacesAbove
    (K := K) (L := L) P
  obtain ⟨q, rfl⟩ := e.surjective Q
  rw [completion_literal_equiv]
  exact completion_norm_canonical P q z

/-- The finite norm at a literal upper prime over `P`. -/
noncomputable def finiteCoordinateNorm
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K)) (Q : PlacesAbovePrime K L P) :
    (Q.1.adicCompletion L)ˣ →* (P.adicCompletion K)ˣ :=
  completionNormLiteral (K := K) (L := L) P Q

set_option maxHeartbeats 5000000 in
-- The subtype equality carried by the literal upper prime is proof-irrelevant
-- but lies inside dependent completion casts.
set_option maxRecDepth 100000 in
/-- At the literal prime represented by a factor, the canonical transported
norm is the original factor-indexed norm. -/
theorem coordinate_norm_equiv
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (q : UpperPrimeFactors (K := K) (L := L) P)
    (z : ((upperPrime (K := K) (L := L) P q).adicCompletion L)ˣ) :
    finiteCoordinateNorm (K := K) (L := L) P
        (upperPlacesAbove
          (K := K) (L := L) P q) z =
      finiteCompletionNorm (K := K) (L := L) P q z := by
  exact completion_literal_equiv P q z

set_option maxHeartbeats 5000000 in
-- Reindexing the dependent completion family through literal primes is deep.
set_option maxRecDepth 100000 in
/-- In a Galois extension, a finite idèle norm coordinate is the product of
the canonical literal-coordinate norms. -/
theorem idele_prod_coordinate
    {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (x : FiniteIdeles (OK L) L) :
    finiteNorm (K := K) (L := L) P x =
      ∏ Q : PlacesAbovePrime K L P,
        finiteCoordinateNorm (K := K) (L := L) P Q (x.1 Q.1) := by
  exact idele_norm_literal P x

private theorem coordinate_norm_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L]
    (P : HeightOneSpectrum (OK K))
    (Q : PlacesAbovePrime K E P)
    (R : PlacesAbovePrime E L Q.1)
    (z : (R.1.adicCompletion L)ˣ) :
    finiteCoordinateNorm (K := K) (L := L) P
        ((placesAboveTower K E L P).symm ⟨Q, R⟩) z =
      finiteCoordinateNorm (K := K) (L := E) P Q
        (finiteCoordinateNorm (K := E) (L := L) Q.1 R z) := by
  rcases Q with ⟨Q, hQ⟩
  subst P
  rcases R with ⟨R, hR⟩
  dsimp at hR ⊢
  subst Q
  simp only [finiteCoordinateNorm]
  rw [completion_literal_canonical,
    completion_literal_canonical,
    completion_literal_canonical]
  dsimp [placesAboveTower]
  have h := finite_canonical_trans (K := K) (E := E) (L := L) R z
  let hUU : (R.under (OK E)).under (OK K) = R.under (OK K) :=
    height_one_spectrum R
  let a : (((R.under (OK E)).under (OK K)).adicCompletion K)ˣ :=
    finiteCanonicalNorm (K := K) (L := E) (R.under (OK E))
      (finiteCanonicalNorm (K := E) (L := L) R z)
  have hval := congrArg Units.val h
  change RingEquiv.cast
      (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K)
      hUU (a : _) =
    (finiteCanonicalNorm (K := K) (L := L) R z : _) at hval
  apply Units.ext
  change RingEquiv.cast
      (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K)
      hUU.symm
      (finiteCanonicalNorm (K := K) (L := L) R z : _) = (a : _)
  rw [← hval]
  change RingEquiv.cast
      (R := fun V : HeightOneSpectrum (OK K) ↦ V.adicCompletion K)
      hUU.symm (RingEquiv.cast hUU (a : _)) = (a : _)
  exact place_cast_symm hUU a

set_option maxHeartbeats 5000000 in
-- Reindexing the dependent finite-prime product exposes the local tower identity.
set_option maxRecDepth 100000 in
/-- Transitivity of the finite component of the concrete idèle norm. -/
theorem idele_norm_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L]
    (x : FiniteIdeles (OK L) L) :
    finiteIdeleNorm (K := K) (L := L) x =
      finiteIdeleNorm (K := K) (L := E)
        (finiteIdeleNorm (K := E) (L := L) x) := by
  apply RestrictedProduct.ext
  intro P
  change finiteNorm (K := K) (L := L) P x =
    finiteNorm (K := K) (L := E) P
      (finiteIdeleNorm (K := E) (L := L) x)
  rw [idele_prod_coordinate,
    idele_prod_coordinate]
  let e := placesAboveTower K E L P
  calc
    (∏ R : PlacesAbovePrime K L P,
        finiteCoordinateNorm (K := K) (L := L) P R (x.1 R.1)) =
        ∏ QR : Σ Q : PlacesAbovePrime K E P,
            PlacesAbovePrime E L Q.1,
          finiteCoordinateNorm (K := K) (L := L) P (e.symm QR)
            (x.1 QR.2.1) := by
      exact (e.symm.prod_comp (fun R ↦
        finiteCoordinateNorm (K := K) (L := L) P R (x.1 R.1))).symm
    _ = ∏ Q : PlacesAbovePrime K E P,
        ∏ R : PlacesAbovePrime E L Q.1,
          finiteCoordinateNorm (K := K) (L := L) P (e.symm ⟨Q, R⟩)
            (x.1 R.1) := Fintype.prod_sigma _
    _ = ∏ Q : PlacesAbovePrime K E P,
        ∏ R : PlacesAbovePrime E L Q.1,
          finiteCoordinateNorm (K := K) (L := E) P Q
            (finiteCoordinateNorm (K := E) (L := L) Q.1 R
              (x.1 R.1)) := by
      apply Finset.prod_congr rfl
      intro Q _
      apply Finset.prod_congr rfl
      intro R _
      exact coordinate_norm_trans P Q R (x.1 R.1)
    _ = ∏ Q : PlacesAbovePrime K E P,
        finiteCoordinateNorm (K := K) (L := E) P Q
          (∏ R : PlacesAbovePrime E L Q.1,
            finiteCoordinateNorm (K := E) (L := L) Q.1 R
              (x.1 R.1)) := by
      apply Finset.prod_congr rfl
      intro Q _
      rw [map_prod]
    _ = ∏ Q : PlacesAbovePrime K E P,
        finiteCoordinateNorm (K := K) (L := E) P Q
          ((finiteIdeleNorm (K := E) (L := L) x).1 Q.1) := by
      apply Finset.prod_congr rfl
      intro Q _
      rw [finite_idele_norm,
        idele_prod_coordinate]

end

end Submission.CField.NIndex
