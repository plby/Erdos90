import Submission.NumberTheory.Locals.RamificationGroups
import Submission.NumberTheory.Locals.UnramifiedExtensions

namespace Submission.NumberTheory.Milne

open IsLocalRing
open scoped Pointwise

theorem maximal_inertia_normal
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain S] [IsLocalRing S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] [(maximalIdeal S).LiesOver p]
    (hp : p ≠ ⊥) :
    ((maximalIdeal S).inertia G).Normal := by
  have hD := stabilizer_maximal_top (R := R) (S := S) (G := G) p hp
  have hstable : ∀ sigma : G, sigma • maximalIdeal S = maximalIdeal S := by
    intro sigma
    exact MulAction.mem_stabilizer_iff.mp (hD ▸ Subgroup.mem_top sigma)
  rw [← ideal_ramification_zero]
  exact ideal_ramification_normal (maximalIdeal S) hstable 0

noncomputable def inertiaResidueGalois
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [IsDedekindDomain S] [IsLocalRing S]
    [Module.Finite R S] [Module.IsTorsionFree R S]
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]
    (p : Ideal R) [p.IsMaximal] [(maximalIdeal S).LiesOver p]
    (hp : p ≠ ⊥) :
    letI : ((maximalIdeal S).inertia G).Normal :=
      maximal_inertia_normal (G := G) p hp
    G ⧸ (maximalIdeal S).inertia G ≃*
      (S ⧸ maximalIdeal S) ≃ₐ[R ⧸ p] S ⧸ maximalIdeal S := by
  letI : ((maximalIdeal S).inertia G).Normal :=
    maximal_inertia_normal (G := G) p hp
  let P := maximalIdeal S
  have hD : MulAction.stabilizer G P = ⊤ :=
    stabilizer_maximal_top p hp
  exact gal_stabilizer_top p P hD

end Submission.NumberTheory.Milne
