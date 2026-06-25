import Submission.Group.ExactDepth


noncomputable section

namespace Submission
namespace TBluepr

theorem NPP.relrank_lemem_relcounts
    (P : NPP)
    {r : ℕ}
    (hr : r ∈ P.RelationCounts) :
    P.relationRank ≤ r := by
  exact Nat.sInf_le hr

/- The same lower-bound statement through the `PPDatum` wrapper. -/

theorem PPDatum.relrank_lemem_relcounts
    (H : PPDatum)
    {r : ℕ}
    (hr : r ∈ H.realizesFiniteNontrivial.RelationCounts) :
    H.relationRank ≤ r := by
  simpa [PPDatum.relationRank] using
    NPP.relrank_lemem_relcounts
      H.realizesFiniteNontrivial hr

/- Pure finite-indexing data for deleting one identity relator.  It does not mention
presented groups: the original range is contained in the union of `{1}` with the reduced
range, and every reduced relator already came from the original family. -/

structure PPDatum.IRRanged
    (H : PPDatum)
    (rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank))
    (i : Fin H.relationRank) : Type where
  reducedRels :
    Fin (H.relationRank - 1) → FreeGroup (Fin H.generatorRank)
  rels_identity_reduced :
    Set.range rels ⊆
      ({1} : Set (FreeGroup (Fin H.generatorRank))) ∪ Set.range reducedRels
  reduced_subset_rels :
    Set.range reducedRels ⊆ Set.range rels

/- The concrete finite reindexing obligation for deleting an identity relator.  This is
purely combinatorial: enumerate the original finite family except for the selected index,
whose value is known to be `1`. -/

theorem PPDatum.idrelator_deletionrange_dataexists
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (i : Fin H.relationRank)
    (hi : rels i = 1) :
    Nonempty
      (PPDatum.IRRanged
        H rels i) := by
  classical
  let reducedIndex : Fin (H.relationRank - 1) → Fin H.relationRank :=
    fun j =>
      if h : j.val < i.val then
        ⟨j.val, by
          have hj : j.val < H.relationRank - 1 := j.isLt
          omega⟩
      else
        ⟨j.val + 1, by
          have hj : j.val < H.relationRank - 1 := j.isLt
          omega⟩
  let reducedRels : Fin (H.relationRank - 1) → FreeGroup (Fin H.generatorRank) :=
    fun j => rels (reducedIndex j)
  refine
    ⟨{
      reducedRels := reducedRels
      rels_identity_reduced := ?_
      reduced_subset_rels := ?_
    }⟩
  · rintro y ⟨j, rfl⟩
    by_cases hji : j = i
    · left
      simp [hji, hi]
    · right
      by_cases hlt : j.val < i.val
      · let k : Fin (H.relationRank - 1) :=
          ⟨j.val, by
            have hi_lt : i.val < H.relationRank := i.isLt
            omega⟩
        refine ⟨k, ?_⟩
        have hidx : reducedIndex k = j := by
          apply Fin.ext
          simp [reducedIndex, k, hlt]
        simp [reducedRels, hidx]
      · have hgt : i.val < j.val := by
          have hne_val : j.val ≠ i.val := by
            intro hv
            exact hji (Fin.ext hv)
          omega
        let k : Fin (H.relationRank - 1) :=
          ⟨j.val - 1, by
            have hj_lt : j.val < H.relationRank := j.isLt
            omega⟩
        have hk_not_lt : ¬ k.val < i.val := by
          dsimp [k]
          omega
        refine ⟨k, ?_⟩
        have hidx : reducedIndex k = j := by
          apply Fin.ext
          simp [reducedIndex, k, hk_not_lt]
          omega
        simp [reducedRels, hidx]
  · rintro y ⟨j, rfl⟩
    exact ⟨reducedIndex j, rfl⟩

/- Normal-closure data after deleting one identity relator.  This is the group-theoretic
content needed for presented groups: the reduced relator family generates the same normal
closure as the original family. -/

structure PPDatum.IDClosur
    (H : PPDatum)
    (rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank))
    (i : Fin H.relationRank) : Type where
  reducedRels :
    Fin (H.relationRank - 1) → FreeGroup (Fin H.generatorRank)
  normalClosure_eq :
    Subgroup.normalClosure (Set.range reducedRels) =
      Subgroup.normalClosure (Set.range rels)

/- Range-level deletion data implies equality of normal closures.  The only group-theoretic
point is that adding the identity to a set of relators does not change its normal closure. -/

def PPDatum.IRRanged.normal_closure_data
    {H : PPDatum}
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {i : Fin H.relationRank}
    (D :
      PPDatum.IRRanged
        H rels i) :
    PPDatum.IDClosur
      H rels i := by
  classical
  refine
    {
      reducedRels := D.reducedRels
      normalClosure_eq := ?_
    }
  apply le_antisymm
  · intro g hg
    let N : Subgroup (FreeGroup (Fin H.generatorRank)) :=
      Subgroup.normalClosure (Set.range rels)
    have hnormal : N.Normal := by
      dsimp [N]
      infer_instance
    have hsubset :
        Set.range D.reducedRels ⊆
          (N : Set (FreeGroup (Fin H.generatorRank))) := by
      intro y hy
      exact Subgroup.subset_normalClosure (D.reduced_subset_rels hy)
    letI : N.Normal := hnormal
    exact Subgroup.normalClosure_le_normal hsubset hg
  · intro g hg
    let N : Subgroup (FreeGroup (Fin H.generatorRank)) :=
      Subgroup.normalClosure (Set.range D.reducedRels)
    have hnormal : N.Normal := by
      dsimp [N]
      infer_instance
    have hsubset :
        Set.range rels ⊆
          (N : Set (FreeGroup (Fin H.generatorRank))) := by
      intro y hy
      rcases D.rels_identity_reduced hy with hident | hred
      · have hy1 : y = 1 := by
          exact Set.mem_singleton_iff.mp hident
        rw [hy1]
        exact Subgroup.one_mem N
      · exact Subgroup.subset_normalClosure hred
    letI : N.Normal := hnormal
    exact Subgroup.normalClosure_le_normal hsubset hg

/- A concrete presentation obtained by deleting one identity relator from a minimal relator
family.  The target relator family has `relationRank - 1` entries and presents the same
finite group.  This is the precise finite-presentation object needed to turn identity of a
minimal relator into a smaller realized relation count. -/

structure PPDatum.IdRelatorDeletionpres
    (H : PPDatum)
    (rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank))
    (i : Fin H.relationRank) : Type where
  reducedRels :
    Fin (H.relationRank - 1) → FreeGroup (Fin H.generatorRank)
  reduced_presents :
    Nonempty
      (PresentedGroup (Set.range reducedRels) ≃*
        H.realizesFiniteNontrivial.carrier)

/- Equality of normal closures transports the original presentation equivalence to the
reduced relator family. -/

def PPDatum.IDClosur.toDeletionPresentation
    {H : PPDatum}
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {i : Fin H.relationRank}
    (D :
      PPDatum.IDClosur
        H rels i)
    (hrels :
      Nonempty
        (PresentedGroup (Set.range rels) ≃*
          H.realizesFiniteNontrivial.carrier)) :
    PPDatum.IdRelatorDeletionpres
      H rels i := by
  classical
  refine
    {
      reducedRels := D.reducedRels
      reduced_presents := ?_
    }
  rcases hrels with ⟨e⟩
  refine ⟨?_⟩
  simpa [PresentedGroup] using
    (QuotientGroup.quotientMulEquivOfEq D.normalClosure_eq).trans e

/- Any deletion presentation immediately witnesses that `relationRank - 1` belongs to the
set of admissible relation counts.  This is just unpacking the definition of
`RelationCounts`, kept separate so the harder presentation-equivalence lemma has a small
target. -/

theorem PPDatum.predrel_rankmemrel_coundelepres
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {i : Fin H.relationRank}
    (D :
      PPDatum.IdRelatorDeletionpres
        H rels i) :
    H.relationRank - 1 ∈ H.realizesFiniteNontrivial.RelationCounts := by
  refine ⟨D.reducedRels, ?_⟩
  exact D.reduced_presents

/- Removing an identity relator from a presentation does not change the presented group.
Mathematically, the normal closure of `Set.range rels` is the same as the normal closure of
the range with that identity generator omitted.  The finite indexing bookkeeping is packaged
as the reduced relator family. -/

theorem PPDatum.id_relatordeletion_presexists
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels :
      Nonempty
        (PresentedGroup (Set.range rels) ≃*
          H.realizesFiniteNontrivial.carrier))
    (i : Fin H.relationRank)
    (hi : rels i = 1) :
    Nonempty
      (PPDatum.IdRelatorDeletionpres
        H rels i) := by
  classical
  rcases
      PPDatum.idrelator_deletionrange_dataexists
        H i hi with
    ⟨R⟩
  let N :
      PPDatum.IDClosur
        H rels i :=
    R.normal_closure_data
  exact ⟨N.toDeletionPresentation hrels⟩

/- The deletion presentation gives the numerical contradiction needed for minimality:
`relationRank - 1` is a realized relation count, so the minimal relation rank is at most
that smaller count. -/

theorem PPDatum.relrank_lepred_idreladele
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {i : Fin H.relationRank}
    (D :
      PPDatum.IdRelatorDeletionpres
        H rels i) :
    H.relationRank ≤ H.relationRank - 1 := by
  have hmem :
      H.relationRank - 1 ∈ H.realizesFiniteNontrivial.RelationCounts :=
    PPDatum.predrel_rankmemrel_coundelepres
      H D
  exact
    PPDatum.relrank_lemem_relcounts
      H hmem

/- If one relator in a minimal presentation is the identity, it can be deleted without
changing the presented group.  Therefore the declared relation rank would be bounded by one
less than itself.  This is the finite-presentation counting part of minimal-relator
irredundancy. -/

theorem PPDatum.relrank_lepred_idrelator
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels :
      Nonempty
        (PresentedGroup (Set.range rels) ≃*
          H.realizesFiniteNontrivial.carrier))
    (i : Fin H.relationRank)
    (hi : rels i = 1) :
    H.relationRank ≤ H.relationRank - 1 := by
  classical
  rcases
      PPDatum.id_relatordeletion_presexists
        H hrels i hi with
    ⟨D⟩
  exact
    PPDatum.relrank_lepred_idreladele
      H D

/- Minimal relator families contain no identity relator.  This packages the preceding
counting lemma in the form needed by the Zassenhaus-exit argument. -/

theorem PPDatum.min_presrelator_neone
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels :
      Nonempty
        (PresentedGroup (Set.range rels) ≃*
          H.realizesFiniteNontrivial.carrier)) :
    ∀ i, rels i ≠ 1 := by
  classical
  intro i hi
  have hle :
      H.relationRank ≤ H.relationRank - 1 :=
    PPDatum.relrank_lepred_idrelator
      H hrels i hi
  have hpos : 0 < H.relationRank :=
    Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  omega

end TBluepr
end Submission
