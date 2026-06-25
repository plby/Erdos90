import Submission.Group.FinitePGS
import Submission.Group.HilbertJenningsFox

noncomputable section

namespace Submission

/--
The filtered-presentation Golod--Shafarevich criterion applied to a minimal
presentation of a finite nontrivial `p`-group.

The minimal relators vanish in mod-`p` abelianization, hence lie in the second
Zassenhaus term.  Bundling that constant depth assignment into a
`FPres` lets the quadratic infinitude criterion rule out a
strict defect `4 * relationRank < generatorRank ^ 2`.
-/
theorem PPDatum.notfourmul_relranklt_genranksq
    (H : PPDatum)
    (hd2 : 2 < H.generatorRank) :
    ¬ 4 * H.relationRank < H.generatorRank * H.generatorRank := by
  intro hquad
  rcases
      H.minzass_depthsmod_pabelianizero
        H.minrelators_havevanishing_modpabeliani with
    ⟨rels, hrels, depth, hmem, hdepth⟩
  let p := H.realizesFiniteNontrivial.p
  let P : Presentation := {
    Gen := Fin H.generatorRank
    rels := Set.range rels
  }
  let D : P.RDepths p := {
    depth := fun _ => 2
    mem_depth := by
      intro r
      rcases r.property with ⟨i, hi⟩
      have hmem2 :
          rels i ∈ zassenhausFiltration p (FreeGroup (Fin H.generatorRank)) 2 :=
        zassenhausFiltration_antitone p (FreeGroup (Fin H.generatorRank))
          (hdepth i) (hmem i)
      change
        (MonoidAlgebra.of (ZMod p) (FreeGroup (Fin H.generatorRank)) r.1 - 1 :
            MonoidAlgebra (ZMod p) (FreeGroup (Fin H.generatorRank))) ∈
          GroupAlgebra.augmentationPower (ZMod p) (FreeGroup (Fin H.generatorRank)) 2
      rw [← hi, GroupAlgebra.augmentationPower,
        ← TBluepr.golod_shafarevich_algebra]
      exact
        GShafar.zassenhaus_filtration_subgroup
          (p := p) (G := FreeGroup (Fin H.generatorRank)) 2 hmem2
  }
  let FP : FPres p := {
    toPresentation := P
    depths := D
  }
  let relatorOfIndex : Fin H.relationRank → P.Relator :=
    fun i => ⟨rels i, Set.mem_range_self i⟩
  have hrelatorOfIndex_surjective : Function.Surjective relatorOfIndex := by
    intro r
    rcases r.property with ⟨i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  letI : Finite P.Relator :=
    Finite.of_surjective relatorOfIndex hrelatorOfIndex_surjective
  let e : PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier :=
    Classical.choice hrels
  letI : Finite P.Group :=
    Finite.of_equiv H.realizesFiniteNontrivial.carrier e.toEquiv.symm
  have hgen : H.generatorRank ≤ FP.generatorCount := by
    change H.generatorRank ≤ Nat.card (Fin H.generatorRank)
    simp
  have hsilent : FP.depths.degreeOneSilent := by
    intro r
    simp [FP, D]
  have hcount : Nat.card FP.toPresentation.Relator ≤ H.relationRank := by
    change Nat.card P.Relator ≤ H.relationRank
    calc
      Nat.card P.Relator ≤ Nat.card (Fin H.relationRank) :=
        Nat.card_le_card_of_surjective relatorOfIndex hrelatorOfIndex_surjective
      _ = H.relationRank := Nat.card_fin H.relationRank
  have hinfinite : Infinite FP.Group :=
    Theorems.golod_shafarevich_silent
      FP hd2 hgen hsilent hcount hquad
  exact (not_finite_iff_infinite.mpr hinfinite) inferInstance

/--
The weak quadratic Golod--Shafarevich bound for every finite nontrivial
`p`-group datum.  Ranks at most two are immediate from positivity of the
relation rank; larger ranks use the filtered-presentation adapter above.
-/
theorem PPDatum.genrank_sqlefour_mulrelrank
    (H : PPDatum) :
    H.generatorRank * H.generatorRank ≤ 4 * H.relationRank := by
  by_cases hd2 : 2 < H.generatorRank
  · exact Nat.le_of_not_gt (H.notfourmul_relranklt_genranksq hd2)
  · have hrel := H.relationRank_pos
    interval_cases H.generatorRank <;> omega

end Submission
