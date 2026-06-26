import Towers.ClassField.NormLimitation.OpenCoreStatement
import Towers.ClassField.NormLimitation.PlaceSelection
import Towers.ClassField.HasseNorm.ModulusUnitCofinality

/-!
# The open-neighborhood input to Lemma VII.9.3

An open subgroup of the idèle class group pulls back to an open subgroup of
the idèle group.  The modulus-unit subgroups form a cofinal family there.
After adjoining the finite support of the modulus to a set of places
containing the archimedean places, the divisors of `p`, and ideal-class
generators, Milne's subgroup

`∏_{v∈S} 1 × ∏_{v∉S} U_v`

is contained in that pullback.
-/

namespace Towers.CField.NLimita

open IsDedekindDomain NumberField Topology
open Towers.CField.LFTheory
open Towers.CField.RCGroups
open Towers.CField.Ideles
open Towers.CField.NIndex
open Towers.CField.KNIndex
open Towers.CField.HNorm

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  RingOfIntegers K

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (OK K) K

/-- The basic open subgroup required in Lemma 9.3 can be chosen while
simultaneously imposing all three arithmetic conditions on `S`. -/
theorem openCoreBridge : OpenCoreBridge.{u} := by
  classical
  intro p K _ _ hp V hV
  let q := QuotientGroup.mk' (principalIdeles (OK K) K)
  let H : Subgroup (IdeleGroup (OK K) K) := V.comap q
  have hHopen : IsOpen (H : Set (IdeleGroup (OK K) K)) := by
    exact hV.preimage QuotientGroup.continuous_mk
  obtain ⟨m, hm⟩ :=
    modulusSubgroupsCofinal (K := K) H hHopen
  obtain ⟨S₀, hInfinite, hDivisors, hClass⟩ :=
    exists_BasePlaces p hp K
  let S : Finset (NumberFieldPlace K) :=
    S₀ ∪ m.finiteSupport.image Sum.inl
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · exact fun v ↦ Finset.mem_union_left _ (hInfinite v)
  · intro v hv
    exact Finset.mem_union_left _ (hDivisors v hv)
  · exact contains_generators_mono K
      hClass Finset.subset_union_left
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := hc
    apply hm
    rw [idele_modulus_subgroup]
    constructor
    · constructor
      · intro P hP
        have hPS : (Sum.inl P : NumberFieldPlace K) ∈ S := by
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
        rw [ha.2.1 P hPS]
        exact (rayLocalSubgroup (K := K) P (m.finite P)).one_mem
      · intro w hw
        have hPS : (Sum.inr w.1 : NumberFieldPlace K) ∈ S :=
          Finset.mem_union_left _ (hInfinite w.1)
        rw [ha.1 w.1 hPS]
        exact (positiveRealSubgroup w).one_mem
    · intro P
      by_cases hPS : (Sum.inl P : NumberFieldPlace K) ∈ S
      · change a.2.1 P ∈ IdeleUnitSubgroup (OK K) K P
        rw [ha.2.1 P hPS]
        exact (IdeleUnitSubgroup (OK K) K P).one_mem
      · exact ha.2.2 P hPS

end

end Towers.CField.NLimita
