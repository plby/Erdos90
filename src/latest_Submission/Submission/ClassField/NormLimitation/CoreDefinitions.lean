import Submission.ClassField.Ideles.GlobalPlace

/-!
# Concrete subgroups in Lemma VII.9.3

The topology and Kummer-theory parts of Lemma 9.3 both use the same two
elementary idèle-class subgroups.  They are isolated here so coordinatewise
proofs can use them without importing the later arithmetic machinery.
-/

namespace Submission.CField.NLimita

open IsDedekindDomain NumberField
open Submission.CField.Ideles

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- The basic subgroup used in the openness step of Lemma 9.3:
coordinates in `S` are equal to one, while finite coordinates outside `S`
are local units.  This is Milne's
`∏_{v∈S} 1 × ∏_{v∉S} U_v`, not the much larger group `ℐ_S`. -/
def outsideNeighborhoodIdeles
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) :
    Subgroup (IdeleGroup (RingOfIntegers K) K) where
  carrier := {a |
    (∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S →
        MulEquiv.piUnits a.1 v = 1) ∧
    (∀ P : HeightOneSpectrum (RingOfIntegers K),
      (Sum.inl P : NumberFieldPlace K) ∈ S → a.2.1 P = 1) ∧
    (∀ P : HeightOneSpectrum (RingOfIntegers K),
      (Sum.inl P : NumberFieldPlace K) ∉ S →
        a.2.1 P ∈ IdeleUnitSubgroup (RingOfIntegers K) K P)}
  one_mem' := by
    refine ⟨?_, fun _ _ ↦ rfl, ?_⟩
    · intro v _
      change MulEquiv.piUnits (1 : (InfiniteAdeleRing K)ˣ) v = 1
      exact congrFun (map_one (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))) v
    · intro P _
      exact (IdeleUnitSubgroup (RingOfIntegers K) K P).one_mem
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      change MulEquiv.piUnits (a.1 * b.1) v = 1
      rw [show MulEquiv.piUnits (a.1 * b.1) v =
          MulEquiv.piUnits a.1 v * MulEquiv.piUnits b.1 v by
        exact congrFun (map_mul (MulEquiv.piUnits :
          (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))
            a.1 b.1) v,
        ha.1 v hv, hb.1 v hv, mul_one]
    · intro P hP
      change a.2.1 P * b.2.1 P = 1
      rw [ha.2.1 P hP, hb.2.1 P hP, mul_one]
    · intro P hP
      exact (IdeleUnitSubgroup (RingOfIntegers K) K P).mul_mem
        (ha.2.2 P hP) (hb.2.2 P hP)
  inv_mem' := by
    intro a ha
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      change MulEquiv.piUnits (a.1⁻¹) v = 1
      rw [show MulEquiv.piUnits (a.1⁻¹) v =
          (MulEquiv.piUnits a.1 v)⁻¹ by
        exact congrFun (map_inv (MulEquiv.piUnits :
          (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ)) a.1) v,
        ha.1 v hv, inv_one]
    · intro P hP
      change (a.2.1 P)⁻¹ = 1
      rw [ha.2.1 P hP, inv_one]
    · intro P hP
      exact (IdeleUnitSubgroup (RingOfIntegers K) K P).inv_mem
        (ha.2.2 P hP)

/-- Idèle classes represented by the preceding basic open subgroup. -/
def outsideUnitClasses
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) : Subgroup (CK K) :=
  (outsideNeighborhoodIdeles K S).map
    (QuotientGroup.mk' (principalIdeles (RingOfIntegers K) K))

/-- The concrete subgroup used in the proof of Lemma 9.3: global `p`th
powers together with idèles which are units outside `S`. -/
def kummerCore
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K)) : Subgroup (CK K) :=
  (powMonoidHom p : CK K →* CK K).range ⊔
    outsideUnitClasses K S

end

end Submission.CField.NLimita
