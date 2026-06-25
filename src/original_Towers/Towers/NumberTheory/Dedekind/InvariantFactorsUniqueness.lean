import Towers.NumberTheory.Dedekind.InvariantFactorsCRT
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Uniqueness invariants for invariant-factor decompositions

The annihilator of a finite direct sum of cyclic quotients is the infimum of their defining
ideals.  Consequently, when those ideals form the descending chain in the invariant-factor
theorem, the last (smallest) ideal is determined by the isomorphism class of the quotient.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

/-- The annihilator of a finite direct sum of quotient modules is the infimum of the quotient
ideals. -/
theorem annihilator_direct_quotients
    (A : Type*) [CommRing A]
    (ι : Type*) [Finite ι] (I : ι → Ideal A) :
    Module.annihilator A (⨁ i, A ⧸ I i) = ⨅ i, I i := by
  letI := Fintype.ofFinite ι
  rw [LinearEquiv.annihilator_eq (DirectSum.linearEquivFunOnFintype A ι _)]
  rw [Module.annihilator_pi]
  simp only [Ideal.annihilator_quotient]

/-- The infimum of a nonempty antitone tuple is its final entry. -/
theorem i_inf_antitone
    {L : Type*} [CompleteLattice L]
    (n : ℕ) (f : Fin (n + 1) → L) (hf : Antitone f) :
    (⨅ i, f i) = f (Fin.last n) := by
  apply le_antisymm
  · exact iInf_le _ _
  · exact le_iInf fun i ↦ hf (Fin.le_last i)

/-- In an invariant-factor presentation, the final ideal is the annihilator of the presented
torsion module. -/
theorem annihilator_quotients_last
    (A : Type*) [CommRing A]
    (n : ℕ) (I : Fin (n + 1) → Ideal A) (hI : Antitone I) :
    Module.annihilator A (⨁ i, A ⧸ I i) = I (Fin.last n) := by
  rw [annihilator_direct_quotients, i_inf_antitone n I hI]

/-- The last ideals in two antitone invariant-factor presentations of isomorphic modules agree.
This is the first uniqueness step in Milne's invariant-factor theorem. -/
theorem invariant_last_linear
    (A : Type*) [CommRing A]
    (m n : ℕ)
    (I : Fin (m + 1) → Ideal A) (J : Fin (n + 1) → Ideal A)
    (hI : Antitone I) (hJ : Antitone J)
    (e : (⨁ i, A ⧸ I i) ≃ₗ[A] (⨁ j, A ⧸ J j)) :
    I (Fin.last m) = J (Fin.last n) := by
  rw [← annihilator_quotients_last A m I hI,
    ← annihilator_quotients_last A n J hJ]
  exact e.annihilator_eq

end Towers.NumberTheory.Milne
