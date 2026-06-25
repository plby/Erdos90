import Submission.ClassField.Reciprocity.Reciprocity
import Submission.ClassField.NormCorrespondence.LocalStatements
import Submission.ClassField.Ideles.Ideles

/-!
# Lemma VII.8.4(a): descent to a subextension

This is the literal finite-layer statement in the text.  If `M` is contained
in `L`, restriction from `L` to `M` carries the `L`-layer of the absolute
abelian Artin map to its `M`-layer.  Hence principal-idèle reciprocity for
`L/K` implies it for `M/K`; no reciprocity hypothesis on the absolute map is
used.
-/

namespace Submission.CField.RExist

open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.Recip

noncomputable section

universe u

/-- **Lemma VII.8.4(a).**  If VII.8.1(a) holds for `L/K`, then it holds
for every finite abelian subextension `M/K` contained in `L`. -/
theorem subextension
    (K : Type u) [Field K] [NumberField K]
    (M L : FASubext K)
    (hML : (M.1 : IntermediateField K (SeparableClosure K)) ≤
      (L.1 : IntermediateField K (SeparableClosure K)))
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hL : TrivialPrincipalIdeles
      (NumberField.RingOfIntegers K) K Gal(L.1/K)
      ((localAbelianRestriction L).comp phi)) :
    TrivialPrincipalIdeles
      (NumberField.RingOfIntegers K) K Gal(M.1/K)
      ((localAbelianRestriction M).comp phi) := by
  intro x
  let q := phi (principalIdele (NumberField.RingOfIntegers K) K x)
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective
    (Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K))) q
  have hLq : localAbelianRestriction L q = 1 := hL x
  change localAbelianRestriction M q = 1
  rw [← hσ] at hLq ⊢
  change localAbelianRestriction L (localAbelianizationMap K σ) = 1 at hLq
  change localAbelianRestriction M (localAbelianizationMap K σ) = 1
  rw [abelian_restriction_quotient] at hLq ⊢
  rw [← MonoidHom.mem_ker,
    IntermediateField.restrictNormalHom_ker] at hLq ⊢
  exact IntermediateField.fixingSubgroup_antitone hML hLq

end

end Submission.CField.RExist
