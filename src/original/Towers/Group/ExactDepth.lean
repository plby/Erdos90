import Towers.Group.FinitePGS


noncomputable section

namespace Towers
namespace TBluepr

structure PPDatum.EMZassde
    (H : PPDatum) : Type where
  rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)
  hrels :
    Nonempty
      (PresentedGroup (Set.range rels) ≃*
        H.realizesFiniteNontrivial.carrier)
  depth : Fin H.relationRank → ℕ
  hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)
  hdepth_exact :
    ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)
  hdepth : ∀ i, 2 ≤ depth i

/- Forgetting exactness recovers the already-formalized minimal presentation with depth lower
bounds.  The proof is intentionally explicit so the later strict-presentation package has a
clear coercion-free bridge back to the older API. -/

theorem PPDatum.EMZassde.toMinimal
    {H : PPDatum}
    (E : PPDatum.EMZassde H) :
    H.MinPresZassdepths := by
  refine ⟨E.rels, ?_, E.depth, ?_, ?_⟩
  · exact E.hrels
  · intro i
    exact E.hmem i
  · intro i
    exact E.hdepth i

structure PPDatum.EDMinpre
    (H : PPDatum)
    (rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank))
    (hrels :
      Nonempty
        (PresentedGroup (Set.range rels) ≃*
          H.realizesFiniteNontrivial.carrier))
    (lowerDepth : Fin H.relationRank → ℕ) : Type where
  depth : Fin H.relationRank → ℕ
  hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)
  hdepth_exact :
    ∀ i, rels i ∉ H.relatorZassenhausFiltration (depth i + 1)
  hdepth_refines : ∀ i, lowerDepth i ≤ depth i

/- A single relator has an exact Zassenhaus depth above a prescribed lower bound when it
lies in that depth, exits at the next depth, and the exact depth still refines the lower
one.  This is the pointwise version of the family-level refinement record above. -/

def PPDatum.RelatorExactDepthabove
    (H : PPDatum)
    (w : FreeGroup (Fin H.generatorRank))
    (lowerDepth : ℕ) : Prop :=
  ∃ depth : ℕ,
    lowerDepth ≤ depth ∧
      w ∈ H.relatorZassenhausFiltration depth ∧
      w ∉ H.relatorZassenhausFiltration (depth + 1)

/- If a relator is known to lie in a lower Zassenhaus term and eventually leaves the deeper
terms, then the first exit point gives an exact depth.  This is a purely order-theoretic
selection step on the natural-number filtration index; the later HMR-specific input is only
the eventual exit. -/

theorem PPDatum.relato_depth_memev
    {H : PPDatum}
    {w : FreeGroup (Fin H.generatorRank)}
    {lowerDepth : ℕ}
    (hmem : w ∈ H.relatorZassenhausFiltration lowerDepth)
    (hexit :
      ∃ depth : ℕ,
        lowerDepth ≤ depth ∧
          w ∉ H.relatorZassenhausFiltration (depth + 1)) :
    PPDatum.RelatorExactDepthabove H w lowerDepth := by
  classical
  let P : ℕ → Prop :=
    fun depth =>
      lowerDepth ≤ depth ∧
        w ∉ H.relatorZassenhausFiltration (depth + 1)
  have hP : ∃ depth, P depth := hexit
  let depth : ℕ := Nat.find hP
  have hdepthP : P depth := Nat.find_spec hP
  have hmem_depth : w ∈ H.relatorZassenhausFiltration depth := by
    by_cases hsame : depth = lowerDepth
    · rw [hsame]
      exact hmem
    · have hlt : lowerDepth < depth := by
        exact lt_of_le_of_ne hdepthP.1 (by
          intro h
          exact hsame h.symm)
      have hpred_lt : depth - 1 < depth := by
        omega
      have hnot_pred : ¬ P (depth - 1) :=
        Nat.find_min hP hpred_lt
      have hlower_pred : lowerDepth ≤ depth - 1 := by
        omega
      have hmem_pred_succ :
          w ∈ H.relatorZassenhausFiltration ((depth - 1) + 1) := by
        by_contra hnot
        exact hnot_pred ⟨hlower_pred, hnot⟩
      have hpos : 1 ≤ depth := by
        omega
      simpa [Nat.sub_add_cancel hpos] using hmem_pred_succ
  exact ⟨depth, hdepthP.1, hmem_depth, hdepthP.2⟩

/- Pointwise exact-depth choices assemble into the family-level refinement record.  The proof
uses classical choice only to package the exact depth function; all three fields of the
refinement are read directly from the pointwise witnesses. -/

def PPDatum.EDMinpre.relator_exact_depths
    {H : PPDatum}
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {hrels :
      Nonempty
        (PresentedGroup (Set.range rels) ≃*
          H.realizesFiniteNontrivial.carrier)}
    {lowerDepth : Fin H.relationRank → ℕ}
    (hexact :
      ∀ i,
        PPDatum.RelatorExactDepthabove
          H (rels i) (lowerDepth i)) :
    PPDatum.EDMinpre
      H rels hrels lowerDepth := by
  classical
  let depth : Fin H.relationRank → ℕ :=
    fun i => Classical.choose (hexact i)
  have hspec :
      ∀ i,
        lowerDepth i ≤ depth i ∧
          rels i ∈ H.relatorZassenhausFiltration (depth i) ∧
          rels i ∉ H.relatorZassenhausFiltration (depth i + 1) := by
    intro i
    exact Classical.choose_spec (hexact i)
  refine
    {
      depth := depth
      hmem := ?_
      hdepth_exact := ?_
      hdepth_refines := ?_
    }
  · intro i
    exact (hspec i).2.1
  · intro i
    exact (hspec i).2.2
  · intro i
    exact (hspec i).1

/- Turning an exact refinement into the exact-depth presentation package is formal once the
original lower depths are known to be at least `2`.  The only arithmetic in the proof is the
transitivity of the lower bound `2 ≤ lowerDepth i ≤ depth i`. -/

def PPDatum.EDMinpre.toExactPresentation
    {H : PPDatum}
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {hrels :
      Nonempty
        (PresentedGroup (Set.range rels) ≃*
          H.realizesFiniteNontrivial.carrier)}
    {lowerDepth : Fin H.relationRank → ℕ}
    (hLower : ∀ i, 2 ≤ lowerDepth i)
    (R :
      PPDatum.EDMinpre
        H rels hrels lowerDepth) :
    PPDatum.EMZassde H := by
  refine
    {
      rels := rels
      hrels := hrels
      depth := R.depth
      hmem := ?_
      hdepth_exact := ?_
      hdepth := ?_
    }
  · intro i
    exact R.hmem i
  · intro i
    exact R.hdepth_exact i
  · intro i
    exact le_trans (hLower i) (R.hdepth_refines i)

/- A package bundling the lower-depth minimal presentation and its exact refinement.  This is
the smaller finite-presentation obligation needed for the HMR cut quotient: choose minimal
relators, keep their known depth-two lower control, and then sharpen those depths to exact
first nonzero Zassenhaus degrees. -/

structure PPDatum.EDRefine
    (H : PPDatum) : Type where
  rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)
  hrels :
    Nonempty
      (PresentedGroup (Set.range rels) ≃*
        H.realizesFiniteNontrivial.carrier)
  lowerDepth : Fin H.relationRank → ℕ
  hlower_mem :
    ∀ i, rels i ∈ H.relatorZassenhausFiltration (lowerDepth i)
  hlower_bound : ∀ i, 2 ≤ lowerDepth i
  refinement :
    PPDatum.EDMinpre
      H rels hrels lowerDepth

/- Forgetting the exact refinement recovers the lower-depth minimal presentation.  This
records that the new package is a genuine refinement of the previous theorem rather than a
replacement with unrelated relators. -/

theorem PPDatum.EDRefine.toMinimalPresentation
    {H : PPDatum}
    (P : PPDatum.EDRefine H) :
    H.MinPresZassdepths := by
  refine ⟨P.rels, ?_, P.lowerDepth, ?_, ?_⟩
  · exact P.hrels
  · intro i
    exact P.hlower_mem i
  · intro i
    exact P.hlower_bound i

/- Keeping the conversion to the exact package separate makes the remaining HMR theorem a
single construction step: produce this refinement package.  All coercions between the lower
and exact presentation APIs are handled here. -/

def PPDatum.EDRefine.toExactPresentation
    {H : PPDatum}
    (P : PPDatum.EDRefine H) :
    PPDatum.EMZassde H := by
  exact
    PPDatum.EDMinpre.toExactPresentation
        P.hlower_bound P.refinement

/- A finite `p`-group quotient separating a free-group word from the identity.  This is the
residual finite-`p` input before relating the quotient kernel to a Zassenhaus term. -/

end TBluepr
end Towers
