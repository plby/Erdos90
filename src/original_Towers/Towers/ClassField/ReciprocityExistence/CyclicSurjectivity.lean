import Towers.ClassField.ReciprocityExistence.CyclicCupCarry
import Towers.ClassField.CrossedProducts.Multiplicative2Comparison
import Towers.ClassField.LocalBrauer.CyclicH2

/-!
# Surjectivity of cup product for the standard cyclic group

The carry calculation identifies cup product by the boundary of the
normalized cyclic character with the inverse in the standard computation
`H²(C, M) = M^C / NM`.  Consequently the cup map is surjective, including
for the trivial cyclic group.
-/

namespace Towers.CField.RExist

open Towers.CField.CProduca
open Towers.CField.LBrauer

noncomputable section

variable (n : ℕ) [NeZero n]
variable (M : Type) [CommGroup M]
  [MulDistribMulAction (Multiplicative (ZMod n)) M]

private abbrev cyclicCoefficientRep :=
  Rep.ofMulDistribMulAction (Multiplicative (ZMod n)) M

/-- An invariant in the multiplicative cyclic model, regarded as a
degree-zero invariant of its additive representation. -/
private def additiveCyclicInvariant
    (pi : CyclicH2.invariants (n := n) (M := M)) :
    (cyclicCoefficientRep n M).ρ.invariants :=
  ⟨Additive.ofMul pi.1, fun g ↦ congrArg Additive.ofMul (pi.2 g)⟩

/-- The explicit cup class is the additive realization of Milne's
multiplicative carry class. -/
theorem boundary_multiplicative_carry
    (pi : CyclicH2.invariants (n := n) (M := M)) :
    standardCupBoundary n M (additiveCyclicInvariant n M pi) =
      multiplicative2Additive
        (MHTwo.mk (CCarry.factorSet pi.1 pi.2)) := by
  rw [standard_boundary_carry,
    multiplicative_2_mk,
    NMCocycl₂.toAdditiveH2]
  apply congrArg (groupCohomology.H2π (cyclicCoefficientRep n M))
  apply groupCohomology.cocycles₂_ext
  intro g h
  change (CCarry.carry g.toAdd h.toAdd : ℤ) •
      Additive.ofMul pi.1 =
    Additive.ofMul (pi.1 ^ CCarry.carry g.toAdd h.toAdd)
  simp

private theorem multiplicative_2_subsingleton
    (h : n = 1) :
    Subsingleton (MHTwo (Multiplicative (ZMod n)) M) := by
  subst n
  constructor
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | _ c d =>
      apply congrArg MHTwo.mk
      apply NMCocycl₂.ext
      rintro ⟨g, k⟩
      have hg : g = 1 := Subsingleton.elim _ _
      have hk : k = 1 := Subsingleton.elim _ _
      subst g
      subst k
      rw [c.map_one_fst, d.map_one_fst]

private theorem standard_cyclic_subsingleton
    (h : n = 1) :
    Subsingleton (groupCohomology.H2 (cyclicCoefficientRep n M)) := by
  have hmul := multiplicative_2_subsingleton n M h
  let e := multiplicativeHCohomology
    (G := Multiplicative (ZMod n)) (M := M)
  constructor
  intro x y
  obtain ⟨x', hx'⟩ := e.surjective (Multiplicative.ofAdd x)
  obtain ⟨y', hy'⟩ := e.surjective (Multiplicative.ofAdd y)
  apply Multiplicative.ofAdd.injective
  rw [← hx', ← hy', hmul.elim x' y']

/-- Cup product by the boundary of the normalized injective character is
onto `H²` for the standard cyclic group. -/
theorem standard_boundary_surjective :
    Function.Surjective (standardCupBoundary n M) := by
  intro z
  by_cases htrivial : n = 1
  · have hsub := standard_cyclic_subsingleton n M htrivial
    refine ⟨0, ?_⟩
    exact hsub.elim _ _
  · have hn : 1 < n := by
      have hn0 := NeZero.ne n
      omega
    let e := CyclicH2.mulInvariantsMod
      (n := n) (M := M) hn
    let comparison := multiplicativeHCohomology
      (G := Multiplicative (ZMod n)) (M := M)
    obtain ⟨x, hx⟩ := comparison.surjective (Multiplicative.ofAdd z)
    obtain ⟨pi, hpi⟩ := QuotientGroup.mk'_surjective
      (CyclicH2.norm (n := n) (M := M)).range (e x)
    have hxcarry :
        x = MHTwo.mk (CCarry.factorSet pi.1 pi.2) := by
      rw [← CyclicH2.symm_mk_carry (n := n) (M := M) hn pi]
      apply e.injective
      rw [e.apply_symm_apply]
      exact hpi.symm
    refine ⟨additiveCyclicInvariant n M pi, ?_⟩
    rw [boundary_multiplicative_carry, ← hxcarry]
    exact congrArg Multiplicative.toAdd hx

end

end Towers.CField.RExist
