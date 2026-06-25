import Towers.Group.PresentedAugmentationBridge


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

/--
Every presented augmentation quotient is nontrivial, hence has positive
`𝔽_p`-dimension.
-/
theorem PPDatum.pres_augquot_finrankpos
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) :
    0 < H.pres_aug_quotfinrank (rels := rels) hrels n := by
  classical
  let p := H.realizesFiniteNontrivial.p
  letI : Fact p.Prime := H.realizesFiniteNontrivial.prime_p
  let e : PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier :=
    Classical.choice hrels
  letI : Finite (PresentedGroup (Set.range rels)) :=
    Finite.of_equiv H.realizesFiniteNontrivial.carrier e.toEquiv.symm
  let J : Ideal (MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))) :=
    GShafar.augmentationIdeal (R := ZMod p) (G := PresentedGroup (Set.range rels))
  have hone_not_mem :
      (1 : MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))) ∉ J := by
    change ¬ ((1 : MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))) ∈
      GShafar.augmentationIdeal (R := ZMod p) (G := PresentedGroup (Set.range rels)))
    rw [GShafar.augmentationIdeal, RingHom.mem_ker]
    simp
  have hJ_ne_top : J ≠ ⊤ := by
    intro hJ
    exact hone_not_mem (by simp [hJ])
  have hpow_ne_top : J ^ (n + 2) ≠ ⊤ := by
    intro hpow
    have hle : J ^ (n + 2) ≤ J := by
      simpa [Submodule.pow_one] using
        (Ideal.pow_le_pow_right (I := J) (show 1 ≤ n + 2 by omega))
    have htop_le :
        (⊤ : Ideal (MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels)))) ≤ J := by
      calc
        ⊤ = J ^ (n + 2) := hpow.symm
        _ ≤ J := hle
    exact hJ_ne_top (top_le_iff.mp htop_le)
  letI :
      Nontrivial
        ((MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))) ⧸ J ^ (n + 2)) :=
    Ideal.Quotient.nontrivial_iff.mpr hpow_ne_top
  have hpos : 0 <
      Module.finrank (ZMod p)
        ((MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))) ⧸ J ^ (n + 2)) :=
    Module.finrank_pos
  simpa [PPDatum.pres_aug_quotfinrank,
    PPDatum.presentedAugmentationQuotient, p, J] using hpos

end Towers
