import Towers.ClassField.ProfiniteCohom.Cochains
import Towers.ClassField.ProfiniteCohom.FiniteDiagram

/-!
# Cochain-level common refinement for Milne II.4.2

This proves the injectivity part of the finite-quotient description before
passing to cohomology: two finite-level cochains with the same inflation
agree after pullback to the intersection of their kernels.
-/

namespace Towers.CField.PCohom

variable {G X : Type} [Group G] [TopologicalSpace G] [MulAction G X]

/-- Inflate a cochain on `G/N`, valued in `N`-fixed points, to a cochain on
`G` with values in the underlying module. -/
def inflatePointCochain (r : ℕ) (N : OpenNormalSubgroup G)
    (f : (Fin r → G ⧸ (N : Subgroup G)) → MulAction.fixedPoints N X) :
    (Fin r → G) → X :=
  fun x ↦ (f (fun i ↦ QuotientGroup.mk' (N : Subgroup G) (x i))).1

/-- Pull a finite-level cochain back from `G/N` to `G/L`, where `L ≤ N`.
Its values are automa fixed by `L`. -/
def refinePointCochain (r : ℕ)
    {L N : OpenNormalSubgroup G} (hLN : L ≤ N)
    (f : (Fin r → G ⧸ (N : Subgroup G)) → MulAction.fixedPoints N X) :
    (Fin r → G ⧸ (L : Subgroup G)) → MulAction.fixedPoints L X :=
  fun x ↦
    ⟨(f (fun i ↦ openNormal hLN (x i))).1,
      fun l ↦ by
        simpa using (f (fun i ↦ openNormal hLN (x i))).2
          ⟨(l : G), hLN l.property⟩⟩

theorem inflate_refine_cochain (r : ℕ)
    {L N : OpenNormalSubgroup G} (hLN : L ≤ N)
    (f : (Fin r → G ⧸ (N : Subgroup G)) → MulAction.fixedPoints N X) :
    inflatePointCochain r L (refinePointCochain r hLN f) =
      inflatePointCochain r N f := by
  funext x
  change
    (f (fun i ↦ openNormal hLN
      (QuotientGroup.mk' (L : Subgroup G) (x i)))).1 =
      (f (fun i ↦ QuotientGroup.mk' (N : Subgroup G) (x i))).1
  congr 2

/-- Cochain-level injectivity in Proposition II.4.2. If two finite-level
cochains have the same inflation, then they agree after pullback to the
common refinement `N ⊓ K`. -/
theorem finite_cochains_inf
    (r : ℕ) {N K : OpenNormalSubgroup G}
    (f : (Fin r → G ⧸ (N : Subgroup G)) → MulAction.fixedPoints N X)
    (g : (Fin r → G ⧸ (K : Subgroup G)) → MulAction.fixedPoints K X)
    (h : inflatePointCochain r N f = inflatePointCochain r K g) :
    refinePointCochain r (show N ⊓ K ≤ N from inf_le_left) f =
      refinePointCochain r (show N ⊓ K ≤ K from inf_le_right) g := by
  funext x
  apply Subtype.ext
  choose y hy using fun i ↦ QuotientGroup.mk_surjective (x i)
  have hxy : (fun i ↦ QuotientGroup.mk' ((N ⊓ K : OpenNormalSubgroup G) : Subgroup G)
      (y i)) = x := by
    funext i
    exact hy i
  subst x
  simpa [inflatePointCochain, refinePointCochain,
    openNormal] using congrFun h y

/-- Cochain-level surjectivity in Proposition II.4.2, stated using the
inflation map above. -/
theorem cochain_inflate_points
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [TopologicalSpace X] [DiscreteTopology X] [ContinuousSMul G X]
    (r : ℕ) (f : (Fin r → G) → X) (hf : Continuous f) :
    ∃ N : OpenNormalSubgroup G,
      ∃ fN : (Fin r → G ⧸ (N : Subgroup G)) → MulAction.fixedPoints N X,
        inflatePointCochain r N fN = f := by
  obtain ⟨N, fN, hfN⟩ := cochain_descends_points r f hf
  exact ⟨N, fN, funext hfN⟩

end Towers.CField.PCohom
