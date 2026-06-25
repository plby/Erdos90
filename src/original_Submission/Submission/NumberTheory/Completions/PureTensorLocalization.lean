import Submission.NumberTheory.Completions.FractionRingBridge

/-!
# Extending completed pure-tensor formulas from integers to fractions

Two maps out of a fraction field agree once they agree on the underlying
domain.  This small wrapper is used to extend the integral pure-tensor
formula for a completed product decomposition to every field element.
-/

namespace Submission.NumberTheory.Milne

open nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

variable {R S K L C F Q : Type u}
  [CommRing R] [CommRing S] [Field K] [Field L]
  [Algebra R S] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L]
  [Algebra R L] [Algebra K L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsLocalization (Algebra.algebraMapSubmonoid S R⁰) L]
  [CommRing C] [Algebra R C]
  [Field F] [Algebra C F] [IsFractionRing C F]
  [Algebra R F] [IsScalarTower R C F]
  [Algebra K F] [IsScalarTower R K F]
  [CommRing Q] [Algebra (C ⊗[R] S) Q]
  [Algebra C Q] [IsScalarTower C (C ⊗[R] S) Q]
  [Algebra F Q] [IsScalarTower C F Q]
  [IsLocalization
    (Algebra.algebraMapSubmonoid (C ⊗[R] S) C⁰) Q]
  [Algebra L Q]

/-- A pure-tensor formula for integral elements extends to the whole upper
fraction field. -/
theorem scalar_tmul_integers
    (hintegral : ∀ s : S,
      scalarFractionTensor
          (R := R) (S := S) (K := K) (L := L)
          (C := C) (F := F) (Q := Q)
          ((1 : F) ⊗ₜ[K] algebraMap S L s) =
        algebraMap L Q (algebraMap S L s))
    (x : L) :
    scalarFractionTensor
        (R := R) (S := S) (K := K) (L := L)
        (C := C) (F := F) (Q := Q) ((1 : F) ⊗ₜ[K] x) =
      algebraMap L Q x := by
  let e := scalarFractionTensor
    (R := R) (S := S) (K := K) (L := L)
    (C := C) (F := F) (Q := Q)
  let g : L →+* Q :=
    e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := K) (A := F) (B := L)).toRingHom
  have hg : g = algebraMap L Q := by
    apply IsLocalization.ringHom_ext S⁰
    ext s
    exact hintegral s
  exact DFunLike.congr_fun hg x

end

end Submission.NumberTheory.Milne
