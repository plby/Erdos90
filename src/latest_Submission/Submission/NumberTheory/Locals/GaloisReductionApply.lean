import Submission.NumberTheory.Locals.UnramifiedExtensions

/-!
# Evaluation of the local unramified reduction equivalence

The reduction equivalence for an unramified local Galois extension is
constructed as a composite through the decomposition group and inertia
quotient.  This file records its action on residue classes explicitly.
-/

namespace Submission.NumberTheory.Milne

noncomputable section

open IsLocalRing
open scoped Pointwise

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsDedekindDomain R] [IsDedekindDomain S]
  [IsLocalRing S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
  (p : Ideal R) [p.IsMaximal] [(maximalIdeal S).LiesOver p]
  [Algebra.IsUnramifiedAt R (maximalIdeal S)]

/-- The canonical local reduction equivalence sends an automorphism to its
induced action on residue classes. -/
theorem galois_unramified_mk
    (hp : p ≠ ⊥) (hP : maximalIdeal S ≠ ⊥)
    (sigma : G) (x : S) :
  galois_unramified_local
        (R := R) (S := S) (G := G) p hp hP sigma
          (Ideal.Quotient.mk (maximalIdeal S) x) =
      Ideal.Quotient.mk (maximalIdeal S) (sigma • x) := by
  let P := maximalIdeal S
  have hD : MulAction.stabilizer G P = ⊤ :=
    stabilizer_maximal_top p hp
  have hI : P.inertia G = ⊥ :=
    inertia_maximal_unramified p hp hP
  let decompositionEquiv : G ≃* MulAction.stabilizer G P :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hD.symm)
  have hN :
      (⊥ : Subgroup (MulAction.stabilizer G P)) =
        (P.inertia G).subgroupOf (MulAction.stabilizer G P) := by
    simp [hI]
  change
    (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P)
        ((QuotientGroup.quotientMulEquivOfEq hN)
          (QuotientGroup.quotientBot.symm (decompositionEquiv sigma)))
          (Ideal.Quotient.mk P x) =
      Ideal.Quotient.mk P (sigma • x)
  rw [QuotientGroup.quotientBot_symm_apply,
    QuotientGroup.quotientMulEquivOfEq_mk,
    Ideal.Quotient.stabilizerQuotientInertiaEquiv_mk,
    Ideal.Quotient.stabilizerHom_apply]
  rfl

end

end Submission.NumberTheory.Milne
