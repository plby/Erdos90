import Towers.ClassField.Shifting.TensorExact
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Milne, Class Field Theory, Remark II.3.12: tensor acyclicity

This file packages the four Tate ranges represented in the project under one
name.  The regular tensor term is proved acyclic from its induced-module
description.

Milne also uses the standard Cartan--Eilenberg tensor lemma: if `A` is
cohomologically trivial after restriction to every subgroup and
`Tor₁ᶻ(M,A)=0`, then the diagonal tensor `M ⊗ A` is cohomologically
trivial.  For the splitting module `C(φ) = C ⊕ I_G`, its Tor condition is
equivalent to `Tor₁ᶻ(M,C)=0` because `I_G` is free abelian.  The notes give
this result without proof, and Mathlib currently defines categorical `Tor`
but has neither this tensor lemma nor the required Tor additivity and
flatness API.  We therefore record exactly that missing source-level input as
an axiom, rather than adding stronger hypotheses to Remark II.3.12.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- Vanishing of the first integral Tor group of the underlying abelian
groups.  This is `Tor₁ᶻ(M,C)`, not Tor over the group ring. -/
def TorOneVanishes (M C : Rep ℤ G) : Prop :=
  IsZero ((((CategoryTheory.Tor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ C)))

/-- The first example in Remark II.3.12: a torsion-free left factor has
zero first integral Tor.  This is recorded alongside the tensor lemma because
Mathlib does not yet relate its flat-module API to categorical `Tor`. -/
axiom torOneVanishes_of_left_torsionFree
    (M C : Rep ℤ G) [Module.IsTorsionFree ℤ M] :
    TorOneVanishes M C

/-- The symmetric example in Remark II.3.12: a torsion-free right factor has
zero first integral Tor. -/
axiom torOneVanishes_of_right_torsionFree
    (M C : Rep ℤ G) [Module.IsTorsionFree ℤ C] :
    TorOneVanishes M C

/-- A representation is Tate-acyclic in every range currently represented
by the project. -/
structure TateAcyclic (A : Rep ℤ G) : Prop where
  positiveCohomology : ∀ n : ℕ, 0 < n →
    IsZero (groupCohomology A n)
  zero : Subsingleton (tateCohomologyZero A)
  negOne : Subsingleton (tateCohomologyOne A)
  positiveHomology : ∀ n : ℕ, 0 < n →
    IsZero (groupHomology A n)

/-- Theorem II.3.10 packaged as Tate acyclicity. -/
theorem tate_acyclic_12 (A : Rep ℤ G)
    (h12 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype A) 1) ∧
      IsZero (groupCohomology (Rep.res H.subtype A) 2)) :
    TateAcyclic A := by
  let h := allDegrees A h12
  exact
    { positiveCohomology := h.1
      zero := h.2.1
      negOne := h.2.2.1
      positiveHomology := h.2.2.2 }

/-- The regular middle term in the tensorized Tate sequence is
Tate-acyclic. -/
theorem tensor_regular_acyclic (M : Rep ℤ G) :
    TateAcyclic (M ⊗ Rep.leftRegular ℤ G) := by
  apply tate_acyclic_12
  intro H
  exact
    ⟨restrict_positive_acyclic M H 1 Nat.zero_lt_one,
      restrict_positive_acyclic M H 2 (by omega)⟩

/-- The standard tensor-acyclicity lemma used, without proof, in Milne's
Remark II.3.12, specialized to Tate's concrete splitting module. -/
axiom tensorSplittingModule_tateAcyclic_of_torOne
    (M C : Rep ℤ G) (φ : groupCohomology.cocycles₂ C)
    (hφ : φ (1, 1) = 0)
    (h12 : ∀ H : Subgroup G,
      IsZero (groupCohomology
        (Rep.res H.subtype (splittingModule C φ hφ)) 1) ∧
      IsZero (groupCohomology
        (Rep.res H.subtype (splittingModule C φ hφ)) 2))
    (hTor : TorOneVanishes M C) :
    TateAcyclic (M ⊗ splittingModule C φ hφ)

end

end Towers.CField.Shifting
