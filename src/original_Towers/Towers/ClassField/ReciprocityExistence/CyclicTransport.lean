import Towers.ClassField.ReciprocityExistence.CyclicCarryTransport
import Towers.ClassField.CrossedProducts.Multiplicative2Comparison
import Towers.ClassField.LocalBrauer.CohomologyTransport

/-!
# Cyclic cup-product surjectivity in arbitrary coordinates

After choosing `Multiplicative (ZMod n) ≃* G`, the transported normalized
character gives a surjective cup-product map from invariant coefficients to
`H²(G,M)`.  This is the cyclic periodicity assertion used in Lemma VII.8.5.
-/

namespace Towers.CField.RExist

open Towers.CField.CProduca
open Towers.CField.LBrauer

noncomputable section

variable (n : ℕ) [NeZero n]
variable (G : Type) [Group G] [Fintype G]
variable (M : Type) [CommGroup M] [MulDistribMulAction G M]

private abbrev coefficientRep := Rep.ofMulDistribMulAction G M

/-- A multiplicative invariant in the pulled-back cyclic model, viewed as
an additive invariant for the original `G`-representation. -/
private def additiveInvariantPulled
    (e : Multiplicative (ZMod n) ≃* G)
    (pi : GroupH2.pulledInvariants (M := M) e) :
    (coefficientRep G M).ρ.invariants := by
  let piG := GroupH2.invariantsMulEquiv e pi
  exact ⟨Additive.ofMul piG.1,
    fun g ↦ congrArg Additive.ofMul (piG.2 g)⟩

/-- The multiplicative carry class transported from the chosen standard
cyclic model to `G`. -/
noncomputable def transportedMultiplicativeCarry
    (e : Multiplicative (ZMod n) ≃* G)
    (pi : GroupH2.pulledInvariants (M := M) e) :
    MHTwo G M := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) M :=
    GroupH2.pulledAction e
  exact (GroupH2.hCyclicModel (M := M) e).symm
    (MHTwo.mk (CCarry.factorSet pi.1 pi.2))

/-- The transported cup class is the additive realization of the
multiplicative carry class transported back from the standard cyclic
model. -/
theorem transported_boundary_carry
    (e : Multiplicative (ZMod n) ≃* G)
    (pi : GroupH2.pulledInvariants (M := M) e) :
    transportedCyclicBoundary n G M e
        (additiveInvariantPulled n G M e pi) =
      multiplicative2Additive
        (transportedMultiplicativeCarry n G M e pi) := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) M :=
    GroupH2.pulledAction e
  rw [transported_cup_carry]
  rw [transportedMultiplicativeCarry]
  change groupCohomology.H2π (coefficientRep G M)
      (transportedCarryCocycle n G M e
        (additiveInvariantPulled n G M e pi)) =
    multiplicative2Additive
      (MHTwo.mk
        (MHTrans.cocycleMap e (MulEquiv.refl M)
          (by intro g m; rfl) (CCarry.factorSet pi.1 pi.2)))
  rw [multiplicative_2_mk,
    NMCocycl₂.toAdditiveH2]
  apply congrArg (groupCohomology.H2π (coefficientRep G M))
  apply groupCohomology.cocycles₂_ext
  intro g h
  change (CCarry.carry (e.symm g).toAdd
        (e.symm h).toAdd : ℤ) • Additive.ofMul pi.1 =
    Additive.ofMul
      (pi.1 ^ CCarry.carry (e.symm g).toAdd (e.symm h).toAdd)
  simp

omit [Fintype G] in
private theorem multiplicative_subsingleton_cyclic
    (e : Multiplicative (ZMod n) ≃* G) (h : n = 1) :
    Subsingleton (MHTwo G M) := by
  subst n
  have hG : ∀ g k : G, g = k := by
    intro g k
    apply e.symm.injective
    exact Subsingleton.elim _ _
  constructor
  intro x y
  induction x, y using Quotient.inductionOn₂ with
  | _ c d =>
      apply congrArg MHTwo.mk
      apply NMCocycl₂.ext
      rintro ⟨g, k⟩
      rw [hG g 1, hG k 1, c.map_one_fst, d.map_one_fst]

omit [Fintype G] in
private theorem h_subsingleton_cyclic
    (e : Multiplicative (ZMod n) ≃* G) (h : n = 1) :
    Subsingleton (groupCohomology.H2 (coefficientRep G M)) := by
  have hmul := multiplicative_subsingleton_cyclic
    n G M e h
  let comparison := multiplicativeHCohomology
    (G := G) (M := M)
  constructor
  intro x y
  obtain ⟨x', hx'⟩ := comparison.surjective (Multiplicative.ofAdd x)
  obtain ⟨y', hy'⟩ := comparison.surjective (Multiplicative.ofAdd y)
  apply Multiplicative.ofAdd.injective
  rw [← hx', ← hy', hmul.elim x' y']

/-- Cup product with the boundary of the transported normalized cyclic
character is onto `H²(G,M)`. -/
theorem transported_boundary_surjective
    (e : Multiplicative (ZMod n) ≃* G) :
    Function.Surjective (transportedCyclicBoundary n G M e) := by
  intro z
  by_cases htrivial : n = 1
  · have hsub := h_subsingleton_cyclic n G M e htrivial
    refine ⟨0, ?_⟩
    exact hsub.elim _ _
  · have hn : 1 < n := by
      have hn0 := NeZero.ne n
      omega
    letI : MulDistribMulAction (Multiplicative (ZMod n)) M :=
      GroupH2.pulledAction e
    let pull := GroupH2.hCyclicModel (M := M) e
    let cyclic := CyclicH2.mulInvariantsMod
      (n := n) (M := M) hn
    let comparison := multiplicativeHCohomology
      (G := G) (M := M)
    obtain ⟨x, hx⟩ := comparison.surjective (Multiplicative.ofAdd z)
    obtain ⟨pi, hpi⟩ := QuotientGroup.mk'_surjective
      (CyclicH2.norm (n := n) (M := M)).range (cyclic (pull x))
    have hxcarry :
        x = transportedMultiplicativeCarry n G M e pi := by
      rw [transportedMultiplicativeCarry]
      rw [← CyclicH2.symm_mk_carry (n := n) (M := M) hn pi]
      apply pull.injective
      rw [pull.apply_symm_apply]
      apply cyclic.injective
      rw [cyclic.apply_symm_apply]
      exact hpi.symm
    refine ⟨additiveInvariantPulled n G M e pi, ?_⟩
    rw [transported_boundary_carry, ← hxcarry]
    exact congrArg Multiplicative.toAdd hx

end

end Towers.CField.RExist
