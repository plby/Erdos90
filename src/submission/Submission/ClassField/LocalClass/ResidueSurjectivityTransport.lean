import Submission.NumberTheory.Locals.LocalUnramifiedDecomposition

namespace Submission.CField.LClass

noncomputable section

open IsLocalRing

/-- Surjectivity of a residue-field algebra map is invariant under compatible
equivalences of the two local rings. -/
theorem residue_surjective_ring
    (R S R' S' : Type*)
    [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [CommRing R'] [IsLocalRing R'] [CommRing S'] [IsLocalRing S']
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    [Algebra R' S'] [IsLocalHom (algebraMap R' S')]
    (eR : R ≃+* R') (eS : S ≃+* S')
    (hcompat : (algebraMap R' S').comp eR.toRingHom =
      eS.toRingHom.comp (algebraMap R S))
    (hsurj : Function.Surjective
      (algebraMap (ResidueField R') (ResidueField S'))) :
    Function.Surjective
      (algebraMap (ResidueField R) (ResidueField S)) := by
  intro y
  obtain ⟨s, rfl⟩ := residue_surjective y
  obtain ⟨x, hx⟩ := hsurj (residue S' (eS s))
  obtain ⟨r, rfl⟩ := residue_surjective x
  rw [ResidueField.algebraMap_residue] at hx
  refine ⟨residue R (eR.symm r), ?_⟩
  rw [ResidueField.algebraMap_residue]
  apply (ResidueField.mapEquiv eS).injective
  rw [ResidueField.mapEquiv_apply, ResidueField.map_residue,
    ResidueField.mapEquiv_apply, ResidueField.map_residue]
  have hr := DFunLike.congr_fun hcompat (eR.symm r)
  change algebraMap R' S' (eR (eR.symm r)) =
    eS (algebraMap R S (eR.symm r)) at hr
  rw [eR.apply_symm_apply] at hr
  exact (congrArg (residue S') hr.symm).trans hx

end

end Submission.CField.LClass
