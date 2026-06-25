import Submission.ClassField.Shifting.BarProjection
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro

/-!
# The explicit chain map underlying homological Shapiro

This identifies Mathlib's derived-functor Shapiro isomorphism with the
concrete bar-resolution projection constructed for Proposition II.3.2(b).
-/

open CategoryTheory Finsupp

namespace Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

set_option maxHeartbeats 2000000 in
-- Elaborating the tensor/projective-resolution composite is expensive.
/-- The explicit inhomogeneous-chain map underlying Shapiro's lemma for
induced coefficients.  Elaborating the tensor/projective-resolution
composite is expensive. -/
def indShapiroChain (H : Subgroup G) [DecidableEq G]
    (A : Rep k H) :
    groupHomology.inhomogeneousChains (Rep.ind H.subtype A) ⟶
      groupHomology.inhomogeneousChains A :=
  (groupHomology.inhomogeneousChainsIso (Rep.ind H.subtype A)).hom ≫
    (groupHomology.coinvariantsTensorResProjectiveResolutionIso
      H A (Rep.barResolution k G)).symm.hom ≫
    ((((Rep.coinvariantsTensor k H).obj A).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (Rep.barProjection (k := k) H)) ≫
    (groupHomology.inhomogeneousChainsIso A).inv

set_option maxHeartbeats 2000000 in
-- Unfolding the derived Shapiro isomorphism requires the same large composite.
/-- Mathlib's derived Shapiro isomorphism is induced by the explicit chain
map `indShapiroChain`. -/
theorem ind_iso_explicit (H : Subgroup G) [DecidableEq G]
    (A : Rep k H) (n : ℕ) :
    (groupHomology.indIso H A n).hom =
      HomologicalComplex.homologyMap (indShapiroChain H A) n := by
  classical
  rw [groupHomology.indIso]
  change
    HomologicalComplex.homologyMap
        ((groupHomology.inhomogeneousChainsIso (Rep.ind H.subtype A)).hom ≫
          (groupHomology.coinvariantsTensorResProjectiveResolutionIso
            H A (Rep.barResolution k G)).symm.hom) n ≫
      (groupHomologyIso A n
        ((resFunctor H.subtype).mapProjectiveResolution
          (barResolution k G))).inv = _
  rw [Rep.homology_bar_inv]
  simp only [indShapiroChain]
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

end

end Rep
