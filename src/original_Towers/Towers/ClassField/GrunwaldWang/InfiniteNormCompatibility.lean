import Towers.ClassField.Reciprocity.IdelicExistence

/-!
# Theorem VIII.2.3: infinite-place norm compatibility

At an infinite place the local Artin datum is already expressed by the
quotient by the completed norm range.  Global reciprocity therefore identifies
the pullback of the idèle-class norm subgroup with that range directly.
-/

namespace Towers.CField.GWang

open IsDedekindDomain NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

set_option maxHeartbeats 1000000 in
-- Kernel comparison unfolds the infinite-place norm quotient equivalence.
omit [NumberField K] in
private theorem ker_range_artin
    (L : FASubext K) [NumberField L.1]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L.1) v)
    (f : v.1.Completionˣ →* Gal(L.1/K))
    (hf : InfiniteLayerArtin L v w f) :
    f.ker = (infiniteCompletionNorm (K := K) (L := L.1) v w).range := by
  obtain ⟨e, he⟩ := hf
  ext x
  rw [MonoidHom.mem_ker, he]
  constructor
  · intro hx
    apply (QuotientGroup.eq_one_iff x).1
    apply e.injective
    simpa using hx
  · intro hx
    have hq : QuotientGroup.mk'
        (infiniteCompletionNorm (K := K) (L := L.1) v w).range x = 1 :=
      (QuotientGroup.eq_one_iff x).2 hx
    rw [hq, map_one]
    rfl

set_option maxHeartbeats 1000000 in
-- The global reciprocity kernel and infinite-place Artin data elaborate together.
/-- At an infinite place, the pullback of the global idèle-class norm
subgroup is the norm range of every completion above that place. -/
theorem infinite_local_compatibility
    (phi : IdeleGroup (RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hphi : ContinuousGlobalArtin phi)
    (hrec : IdeleReciprocityLaw (K := K))
    (L : FASubext K)
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L.1) v) :
    (ideleClassSubgroup L).comap
      ((QuotientGroup.mk' (principalIdeles (RingOfIntegers K) K)).comp
        (infinitePlaceEmbedding (RingOfIntegers K) K v)) =
      (infiniteCompletionNorm (K := K) (L := L.1) v w).range := by
  letI : NumberField L.1 := NumberField.of_module_finite K L.1
  obtain ⟨f, hf, hcompat⟩ := hphi.2.2 L v w
  have hkernel := (hrec phi hphi).2 L |>.2
  rw [← ker_range_artin L v w f hf]
  change ((ideleClassSubgroup L).comap
      (QuotientGroup.mk' (principalIdeles (RingOfIntegers K) K))).comap
        (infinitePlaceEmbedding (RingOfIntegers K) K v) = f.ker
  rw [comap_idele_subgroup, hkernel]
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.mem_ker]
  change localAbelianRestriction L
      (phi (infinitePlaceEmbedding (RingOfIntegers K) K v x)) = 1 ↔
    f x = 1
  rw [hcompat x]

end

end Towers.CField.GWang
