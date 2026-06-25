import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Pi

/-!
# Common-denominator localization of finite products

For finitely many algebras, localizing every coordinate at the nonzero
elements of one common base ring is the same as localizing the product at
the diagonal image of those elements.
-/

namespace Submission.NumberTheory.Milne

open nonZeroDivisors

noncomputable section

universe u

/-- A finite product of coordinate localizations at `C⁰` is the
localization of the product at the diagonal image of `C⁰`. -/
theorem submonoid_non_divisors
    {C ι : Type*} (B L : ι → Type u)
    [CommRing C] [Finite ι]
    [∀ i, CommRing (B i)] [∀ i, CommRing (L i)]
    [∀ i, Algebra C (B i)] [∀ i, Algebra (B i) (L i)]
    [∀ i, IsLocalization
      (Algebra.algebraMapSubmonoid (B i) C⁰) (L i)] :
    letI : Algebra (∀ i, B i) (∀ i, L i) := inferInstance
    IsLocalization
      (Algebra.algebraMapSubmonoid (∀ i, B i) C⁰) (∀ i, L i) := by
  letI : Algebra (∀ i, B i) (∀ i, L i) := inferInstance
  let M := Algebra.algebraMapSubmonoid (∀ i, B i) C⁰
  rw [IsLocalization.iff_map_piEvalRingHom B (∀ i, L i) M]
  letI := Fintype.ofFinite ι
  have hM (i : ι) :
      M.map (Pi.evalRingHom B i) =
        Algebra.algebraMapSubmonoid (B i) C⁰ := by
    ext b
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨algebraMap C (∀ i, B i) c, ⟨c, hc, rfl⟩, ?_⟩
      rfl
  haveI (i : ι) :
      IsLocalization (M.map (Pi.evalRingHom B i)) (L i) := by
    rw [hM i]
    infer_instance
  infer_instance

end

end Submission.NumberTheory.Milne
