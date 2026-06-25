import Towers.ClassField.Ideles.GlobalPlace

/-!
# The concrete idèle subgroup in Lemma VII.6.4

This file isolates the elementary definition of Milne's subgroup `E` from
the arithmetic norm-lifting statements used later in Lemma 6.4.  In
particular, coordinatewise arguments about `E` do not need to import the
idèle extension map.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.CField.Ideles

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- The subgroup of `p`th powers in a commutative multiplicative group. -/
abbrev pthPowerSubgroup (p : ℕ) (G : Type u) [CommGroup G] : Subgroup G :=
  (powMonoidHom p : G →* G).range

/-- The finite coordinate of an actual number-field idèle. -/
abbrev finiteCoordinate
    (K : Type u) [Field K] [NumberField K]
    (a : IdeleGroup (OK K) K) (P : HeightOneSpectrum (OK K)) :
    (P.adicCompletion K)ˣ :=
  a.2.1 P

/-- The infinite coordinate of an actual number-field idèle. -/
abbrev infiniteCoordinate
    (K : Type u) [Field K] [NumberField K]
    (a : IdeleGroup (OK K) K) (v : InfinitePlace K) : v.Completionˣ :=
  MulEquiv.piUnits a.1 v

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent completion-coordinate subgroups require substantial
-- typeclass search while the three closure fields are elaborated.
set_option maxHeartbeats 1000000 in
/-- Milne's concrete subgroup

`E = ∏_{v∈S} K_v^{×p} × ∏_{v∈T} K_v×
       × ∏_{v∉S∪T} U_v`.

The ambient setup requires every infinite place to lie in `S`; that
requirement is retained separately by the norm-lifting theorem. Thus the
last, local-unit condition is only a condition at finite primes. -/
def ideleSubgroup
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (HeightOneSpectrum (OK K))) : Subgroup (IdeleGroup (OK K) K) where
  carrier := {a |
    (∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S →
        infiniteCoordinate K a v ∈
          pthPowerSubgroup p v.Completionˣ) ∧
    (∀ P : HeightOneSpectrum (OK K),
      (Sum.inl P : NumberFieldPlace K) ∈ S →
        finiteCoordinate K a P ∈
          pthPowerSubgroup p (P.adicCompletion K)ˣ) ∧
    (∀ P : HeightOneSpectrum (OK K),
      (Sum.inl P : NumberFieldPlace K) ∉ S → P ∉ T →
        finiteCoordinate K a P ∈
          IdeleUnitSubgroup (OK K) K P)}
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro v _
      exact (pthPowerSubgroup p v.Completionˣ).one_mem
    · intro P _
      exact (pthPowerSubgroup p (P.adicCompletion K)ˣ).one_mem
    · intro P _ _
      exact (IdeleUnitSubgroup (OK K) K P).one_mem
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact (pthPowerSubgroup p v.Completionˣ).mul_mem
        (ha.1 v hv) (hb.1 v hv)
    · intro P hP
      exact (pthPowerSubgroup p (P.adicCompletion K)ˣ).mul_mem
        (ha.2.1 P hP) (hb.2.1 P hP)
    · intro P hPS hPT
      exact (IdeleUnitSubgroup (OK K) K P).mul_mem
        (ha.2.2 P hPS hPT) (hb.2.2 P hPS hPT)
  inv_mem' := by
    intro a ha
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact (pthPowerSubgroup p v.Completionˣ).inv_mem (ha.1 v hv)
    · intro P hP
      exact (pthPowerSubgroup p (P.adicCompletion K)ˣ).inv_mem
        (ha.2.1 P hP)
    · intro P hPS hPT
      exact (IdeleUnitSubgroup (OK K) K P).inv_mem
        (ha.2.2 P hPS hPT)

end

end Towers.CField.KNIndex
