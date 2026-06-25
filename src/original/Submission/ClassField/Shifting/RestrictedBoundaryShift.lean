import Submission.ClassField.Shifting.ZeroResTop

/-!
# Milne, Class Field Theory, Theorem II.3.11: source-faithful statement

The implementation theorem takes the cardinality of the ambient degree-two
cohomology group as a separate argument.  Milne does not: his subgroup
hypothesis explicitly includes the top subgroup.  This file derives that
ambient equality from the top-subgroup instance and exposes the theorem with
no redundant cardinality hypothesis.
-/

namespace Submission.CField.Shifting

open AddSubgroup CategoryTheory.Limits Rep Representation

noncomputable section

variable {G : Type} [Group G] [Fintype G]

/-- **Theorem II.3.11 (Tate).** If `H¹(H,C)` vanishes and `H²(H,C)` has
order `|H|` for every subgroup `H`, then a chosen generator `gamma` of
`H²(G,C)` determines the two-degree Tate shift.  The ambient cardinality
equality is the case `H = G` of the stated subgroup hypothesis, rather than
an additional input. -/
noncomputable def restrictedShiftStatement
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hcardH : ∀ H : Subgroup G,
      Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H) :
    TateTwoShift C := by
  apply cohomologyResTop C gamma hgamma
  · calc
      Nat.card (groupCohomology C 2) =
          Nat.card (groupCohomology
            (Rep.res (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom C) 2) :=
        Nat.card_congr
          (cohomologyMulIso
            (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G) C 2).toLinearEquiv.toEquiv
      _ = Nat.card (⊤ : Subgroup G) := hcardH ⊤
      _ = Nat.card G := Subgroup.card_top
  · exact hC1
  · exact hcardH

end

end Submission.CField.Shifting
