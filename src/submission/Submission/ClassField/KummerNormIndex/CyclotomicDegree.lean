import Mathlib.NumberTheory.Cyclotomic.Gal
import Submission.ClassField.KummerNormIndex.IdeleClassQuotient

namespace Submission.CField.KNIndex

noncomputable section

universe u

/-- The degree of the field obtained by adjoining a primitive `p`th root
of unity divides `p - 1`.  This is the degree assertion used in Milne's
cyclotomic reduction: Galois automorphisms act faithfully on the primitive
root, hence embed in `(ZMod p)ˣ`. -/
theorem cyclotomic_dvd_pred
    {p : ℕ} (hp : Nat.Prime p)
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    [IsCyclotomicExtension {p} K E] :
    Module.finrank K E ∣ p - 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : FiniteDimensional K E :=
    IsCyclotomicExtension.finiteDimensional {p} K E
  letI : IsGalois K E := IsCyclotomicExtension.isGalois {p} K E
  let zeta := IsCyclotomicExtension.zeta p K E
  have hzeta : IsPrimitiveRoot zeta p :=
    IsCyclotomicExtension.zeta_spec p K E
  have hdiv : Nat.card Gal(E/K) ∣ Nat.card (ZMod p)ˣ :=
    Subgroup.card_dvd_of_injective (hzeta.autToPow K)
      (hzeta.autToPow_injective K)
  rw [IsGalois.card_aut_eq_finrank K E] at hdiv
  simpa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime hp] using hdiv

end

end Submission.CField.KNIndex
