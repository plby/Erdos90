import Submission.ClassField.Shifting.SubsingletonLinearEquiv
import Submission.ClassField.UnramifiedCohom.FiniteFieldTraces

/-!
# Milne, Class Field Theory, Lemma III.1.5

The additive group of a finite residue-field extension is Tate-acyclic.
The separately exposed theorem `field_trace_surjective` is the trace
consequence stated in the source.
-/

namespace Submission.CField.UCohom

open CategoryTheory Representation
open Submission.CField.Shifting

noncomputable section

attribute [local instance] IsCyclic.commGroup

/-- **Lemma III.1.5, all Tate degrees.**  For a finite extension `l/k` of
finite fields, the additive Galois module `l` has trivial Tate cohomology in
every degree.

The four clauses are positive cohomology, degrees zero and minus one, and
positive homology (the Tate degrees below minus one). -/
theorem additive_tate_acyclic
    (k l : Type) [Field k] [Field l] [Algebra k l] [Finite l] :
    let A := COps.additiveGaloisRepresentation k l
    (∀ n : ℕ, 0 < n → Subsingleton (groupCohomology A n)) ∧
      Subsingleton (tateCohomologyZero A) ∧
      Subsingleton (tateCohomologyOne A) ∧
      ∀ n : ℕ, 0 < n → Subsingleton (groupHomology A n) := by
  let A := COps.additiveGaloisRepresentation k l
  obtain ⟨g, hgpow⟩ :=
    IsCyclic.exists_monoid_generator (α := Gal(l/k))
  have hg : ∀ x, x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨n, hn⟩ := hgpow x
    refine ⟨(n : ℤ), ?_⟩
    simpa using hn
  have h₁ : Subsingleton (groupCohomology A 1) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (cohomology_additive_extension
        k l 1 Nat.zero_lt_one)
  have h₂ : Subsingleton (groupCohomology A 2) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (cohomology_additive_extension
        k l 2 (by omega))
  exact tate_subsingleton_cyclic A g hg h₁ h₂

end

end Submission.CField.UCohom
