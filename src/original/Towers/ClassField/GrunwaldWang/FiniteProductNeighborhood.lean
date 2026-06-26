import Towers.ClassField.GrunwaldWang.SimultaneousStatement
import Towers.ClassField.GrunwaldWang.CompletionNormCompatibility
import Towers.ClassField.GrunwaldWang.FiniteProduct
import Towers.ClassField.GrunwaldWang.InfiniteNormCompatibility
import Towers.ClassField.NormLimitation.ExistenceStatement
import Towers.ClassField.Reciprocity.IdelicExistence
import Towers.NumberTheory.Locals.PlaceExtension

namespace Towers.CField.GWang

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.NLimita

noncomputable section
universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The sole remaining Artin--Tate topology input from the paragraph before
VIII.2.3.  For the finite product of the selected local multiplicative
groups, every product of open finite-index subgroups contains the pullback of
some open finite-index subgroup of the idèle class group.

This is strictly weaker than `GlobalSubgroupBridge`: it asks only
for containment of one pullback.  The finite-family extension lemma enlarges
that subgroup to obtain equality at every selected place. -/
def FiniteProductNeighborhood : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (Place K))
    (N : ∀ v : S, Subgroup (LocalMultiplicativeGroup K v.1)),
    (∀ v : S, OFSubgro (N v)) →
      ∃ V : Subgroup (IdeleClassGroup (RingOfIntegers K) K),
        IsOpen (V : Set (IdeleClassGroup (RingOfIntegers K) K)) ∧
        V.FiniteIndex ∧
        V.comap (placeIdeleHom K S) ≤
          finiteFamilySubgroup
            (fun v : S => LocalMultiplicativeGroup K v.1) N

/-- The idèle topology/approximation step: finitely many prescribed local
subgroups are simultaneous pullbacks of one open finite-index class-group
subgroup. -/
def GlobalSubgroupBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (S : Finset (Place K))
    (N : ∀ v : S, Subgroup (LocalMultiplicativeGroup K v.1)),
    (∀ v : S, OFSubgro (N v)) →
      ∃ U : Subgroup (IdeleClassGroup (RingOfIntegers K) K),
        IsOpen (U : Set (IdeleClassGroup (RingOfIntegers K) K)) ∧
        U.FiniteIndex ∧
        ∀ v : S, U.comap (placeClassHom K v.1) = N v

/-- The exact small-neighborhood assertion from Artin--Tate implies the
simultaneous equality formulation used in Theorem VIII.2.3.  All finite
product and subgroup-enlargement bookkeeping is formal here. -/
theorem global_bridge_neighborhood
    (hsmall : FiniteProductNeighborhood.{u}) :
    GlobalSubgroupBridge.{u} := by
  intro K _ _ S N hN
  obtain ⟨V, hVopen, hVfinite, hVsmall⟩ := hsmall K S N hN
  exact open_comap_family
    (fun v : S => LocalMultiplicativeGroup K v.1)
    (IdeleClassGroup (RingOfIntegers K) K)
    (fun v => placeClassHom K v.1) N
    V hVopen hVfinite hVsmall

set_option synthInstance.maxHeartbeats 300000 in
-- Local completion and norm-subgroup instances are synthesized simultaneously.
set_option maxHeartbeats 3000000 in
-- The finite product of local norm neighborhoods needs a larger reduction budget.
/-- Local-global norm compatibility from the reciprocity laws used in the
source: the pullback of a global class norm group at `v` is the norm range of
a completion above `v`. -/
theorem localNormCompatibility
    (hArtin : GlobalArtinProposition (K := K))
    (hrec : IdeleReciprocityLaw (K := K))
    (L : FASubext K) (v : Place K) :
    RealizesLocalSubgroup K L v
      ((ideleClassSubgroup L).comap (placeClassHom K v)) := by
  letI : NumberField L.1 := NumberField.of_module_finite K L.1
  obtain ⟨phi, hphi, _⟩ := hArtin
  cases v with
  | inl P =>
      haveI : P.asIdeal.IsMaximal := P.isPrime.isMaximal P.ne_bot
      obtain ⟨Q, hQ⟩ :=
        finite_places_nonempty
          (L := L.1) P.asIdeal
      have hQfactor : Q ∈
          IsDedekindDomain.primesOverFinset P.asIdeal (RingOfIntegers L.1) :=
        (IsDedekindDomain.mem_primesOverFinset_iff P.ne_bot (RingOfIntegers L.1)).2 hQ
      let Qfactor : UpperPrimeFactors (K := K) (L := L.1) P :=
        ⟨Q, hQfactor⟩
      obtain ⟨f, hf, hcompat⟩ := hphi.2.1 L P Qfactor
      obtain ⟨w, hwv, hwq, hfinite, hlocalKernel⟩ :=
        artin_ker_abstract L P Qfactor f hf
      have hcompletion := completion_norm_range
        (K := K) (L := L.1) P Qfactor w hwv hwq hfinite
      have hglobalKernel := (hrec phi hphi).2 L |>.2
      have hpullback :
          (ideleClassSubgroup L).comap
              ((QuotientGroup.mk'
                (principalIdeles (RingOfIntegers K) K)).comp
                (finitePlaceEmbedding (RingOfIntegers K) K P)) =
            f.ker := by
        change ((ideleClassSubgroup L).comap
            (QuotientGroup.mk'
              (principalIdeles (RingOfIntegers K) K))).comap
              (finitePlaceEmbedding (RingOfIntegers K) K P) = f.ker
        rw [comap_idele_subgroup, hglobalKernel]
        ext x
        simp only [Subgroup.mem_comap, MonoidHom.mem_ker]
        change (localAbelianRestriction L)
            (phi (finitePlaceEmbedding (RingOfIntegers K) K P x)) = 1 ↔
          f x = 1
        rw [hcompat x]
      refine ⟨Qfactor, ?_⟩
      exact (hpullback.trans (hlocalKernel.trans hcompletion)).symm
  | inr v =>
      obtain ⟨w, hw⟩ := infinite_place (L := L.1) v
      let wAbove : InfinitePlacesAbove (K := K) (L := L.1) v := ⟨w, hw⟩
      refine ⟨wAbove, ?_⟩
      exact (infinite_local_compatibility
        phi hphi hrec L v wAbove).symm

/-- Theorem VIII.2.3 follows from the idelic existence theorem and the two
literal compatibility steps above. -/
theorem simultaneous_existence_bridges
    (h95 : EveryIndexGroup K)
    (hglobal : GlobalSubgroupBridge.{u})
    (hArtin : GlobalArtinProposition (K := K))
    (hrec : IdeleReciprocityLaw (K := K)) :
    SimultaneousExistenceTheorem K := by
  intro S N hN
  obtain ⟨U, hUopen, hUfinite, hpullback⟩ := hglobal K S N hN
  obtain ⟨L, hL⟩ := h95 U hUopen hUfinite
  refine ⟨L, fun v => ?_⟩
  rw [← hpullback v, ← hL]
  exact localNormCompatibility K hArtin hrec L v.1

end
end Towers.CField.GWang
