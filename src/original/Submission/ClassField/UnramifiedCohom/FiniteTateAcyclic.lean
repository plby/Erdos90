import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Submission.ClassField.Shifting.NormTransitivity
import Submission.ClassField.UnramifiedCohom.FiniteFieldNorms
import Submission.ClassField.UnramifiedCohom.CohomologicalReduction
import Submission.ClassField.LocalReciprocity.TateZeroQuotient

/-!
# Milne, Class Field Theory, Lemma III.1.4

The multiplicative group of a finite residue-field extension is
Tate-acyclic.  Together with `units_norm_surjective`, this gives
both assertions of the source lemma.
-/

namespace Submission.CField.UCohom

open CategoryTheory Representation
open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.LRecip

noncomputable section

attribute [local instance] IsCyclic.commGroup

/-- **Lemma III.1.4, all Tate degrees.**  For a finite extension `l/k` of
finite fields, the multiplicative Galois module `lˣ` has trivial Tate
cohomology in every degree.

The four clauses are the project's representation of the integer-indexed
Tate groups: positive cohomology, degrees zero and minus one, and positive
homology (the degrees below minus one). -/
theorem units_tate_acyclic
    (k l : Type) [Field k] [Field l] [Algebra k l] [Finite l] :
    let A : Rep ℤ Gal(l/k) := Rep.ofMulDistribMulAction Gal(l/k) lˣ
    (∀ n : ℕ, 0 < n → Subsingleton (groupCohomology A n)) ∧
      Subsingleton (tateCohomologyZero A) ∧
      Subsingleton (tateCohomologyOne A) ∧
      ∀ n : ℕ, 0 < n → Subsingleton (groupHomology A n) := by
  let A : Rep ℤ Gal(l/k) := Rep.ofMulDistribMulAction Gal(l/k) lˣ
  obtain ⟨g, hgpow⟩ :=
    IsCyclic.exists_monoid_generator (α := Gal(l/k))
  have hg : ∀ x, x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨n, hn⟩ := hgpow x
    refine ⟨(n : ℤ), ?_⟩
    simpa using hn
  have hzero : Subsingleton (tateCohomologyZero A) := by
    have hnorm : Function.Surjective
        (Submission.CField.LFTheory.normOnUnits k l) :=
      units_norm_surjective k l
    have hrange : Submission.CField.LFTheory.normSubgroup k l = ⊤ :=
      MonoidHom.range_eq_top.mpr hnorm
    have hquot : Subsingleton
        (kˣ ⧸ Submission.CField.LFTheory.normSubgroup k l) :=
      QuotientGroup.subsingleton_iff.mpr hrange
    letI : Subsingleton
        (kˣ ⧸ Submission.CField.LFTheory.normSubgroup k l) := hquot
    letI : Subsingleton
        (Additive (kˣ ⧸ Submission.CField.LFTheory.normSubgroup k l)) :=
      inferInstance
    exact
      (galoisTateQuotient k l).injective.subsingleton
  have hnormRep : Function.Surjective
      (normCoinvariantsInvariants A) :=
    (coinvariants_invariants_surjective A).2 hzero
  have h₁ : Subsingleton (groupCohomology A 1) := by
    change Subsingleton
      (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits k l))
    infer_instance
  exact tate_acyclic_surjective
    A g hg h₁ hnormRep

end

end Submission.CField.UCohom
