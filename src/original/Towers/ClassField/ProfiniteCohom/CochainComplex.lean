import Towers.ClassField.ProfiniteCohom.CochainRefinement

/-!
# Cochain complexes for Milne II.4.2

This file exposes the cochain maps underlying the finite-quotient inflation
diagram.  In degree `r` they are precisely pullback along `G/L → G/N`
together with the inclusion `A^N ⊆ A^L`, and their chain-map square is the
usual inhomogeneous-cochain differential compatibility.
-/

namespace Towers.CField.PCohom

open CategoryTheory

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]

/-- The inhomogeneous cochain complex `C•(G/N, A^N)` at a finite-quotient
level in Milne's system. -/
abbrev finiteQuotientCochains (A : Rep ℤ G) (N : OpenNormalSubgroup G) :=
  groupCohomology.inhomogeneousCochains
    (A.quotientToInvariants (N : Subgroup G))

/-- Refa from the level `N` to the finer level `L ≤ N`, as a map of
inhomogeneous cochain complexes. -/
def finiteCochainRefinement (A : Rep ℤ G)
    {L N : OpenNormalSubgroup G} (hLN : L ≤ N) :
    finiteQuotientCochains A N ⟶ finiteQuotientCochains A L :=
  groupCohomology.cochainsMap (openNormal hLN)
    (inflationCoefficientMap A hLN)

/-- The degree-`r` linear refinement map on finite-quotient cochains. -/
def cochainRefinementLinear (A : Rep ℤ G)
    {L N : OpenNormalSubgroup G} (hLN : L ≤ N) (r : ℕ) :
    (finiteQuotientCochains A N).X r →ₗ[ℤ]
      (finiteQuotientCochains A L).X r :=
  ((finiteCochainRefinement A hLN).f r).hom

/-- Pointwise, refinement is pullback along `G/L → G/N`, followed by the
canonical inclusion of invariant coefficient modules. -/
@[simp]
theorem cochain_refinement_linear (A : Rep ℤ G)
    {L N : OpenNormalSubgroup G} (hLN : L ≤ N) (r : ℕ)
    (f : (finiteQuotientCochains A N).X r)
    (x : Fin r → G ⧸ (L : Subgroup G)) :
    cochainRefinementLinear A hLN r f x =
      inflationCoefficientMap A hLN
        (f (fun i ↦ openNormal hLN (x i))) := by
  rfl

/-- On underlying coefficient values, refinement changes nothing; it only
regards an `N`-fixed value as an `L`-fixed value. -/
@[simp]
theorem cochain_refinement_val (A : Rep ℤ G)
    {L N : OpenNormalSubgroup G} (hLN : L ≤ N) (r : ℕ)
    (f : (finiteQuotientCochains A N).X r)
    (x : Fin r → G ⧸ (L : Subgroup G)) :
    (cochainRefinementLinear A hLN r f x).1 =
      (f (fun i ↦ openNormal hLN (x i))).1 := by
  rfl

/-- Refa commutes with the ordinary inhomogeneous differential. -/
theorem finite_refinement_d (A : Rep ℤ G)
    {L N : OpenNormalSubgroup G} (hLN : L ≤ N) (r : ℕ) :
    inhomogeneousCochains.d
          (A.quotientToInvariants (N : Subgroup G)) r ≫
        (finiteCochainRefinement A hLN).f (r + 1) =
      (finiteCochainRefinement A hLN).f r ≫
        inhomogeneousCochains.d
          (A.quotientToInvariants (L : Subgroup G)) r := by
  rw [← groupCohomology.inhomogeneousCochains.d_def,
    ← groupCohomology.inhomogeneousCochains.d_def]
  exact (finiteCochainRefinement A hLN).comm r (r + 1) |>.symm

/-- Elementwise differential compatibility.  This is the concrete identity
needed to descend cocycles and coboundaries through the finite levels. -/
theorem cochain_refinement_d (A : Rep ℤ G)
    {L N : OpenNormalSubgroup G} (hLN : L ≤ N) (r : ℕ)
    (f : (finiteQuotientCochains A N).X r) :
    cochainRefinementLinear A hLN (r + 1)
        ((inhomogeneousCochains.d
          (A.quotientToInvariants (N : Subgroup G)) r).hom f) =
      (inhomogeneousCochains.d
        (A.quotientToInvariants (L : Subgroup G)) r).hom
        (cochainRefinementLinear A hLN r f) := by
  have h := congrArg (fun φ ↦ φ f)
    (finite_refinement_d A hLN r)
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, cochainRefinementLinear] using h

@[simp]
theorem cochain_refinement_refl (A : Rep ℤ G)
    (N : OpenNormalSubgroup G) :
    finiteCochainRefinement A (show N ≤ N from le_rfl) = 𝟙 _ := by
  ext i
  apply DFunLike.ext _ _
  intro f
  funext x
  dsimp [finiteCochainRefinement, groupCohomology.cochainsMap]
  dsimp [inflationCoefficientMap]
  apply Subtype.ext
  change (f (openNormal le_rfl ∘ x)).1 = (f x).1
  apply congrArg (fun y ↦ (f y).1)
  funext j
  exact QuotientGroup.map_id_apply (N : Subgroup G) _ (x j)

theorem cochain_refinement_trans (A : Rep ℤ G)
    {L K N : OpenNormalSubgroup G} (hLK : L ≤ K) (hKN : K ≤ N) :
    finiteCochainRefinement A hKN ≫
        finiteCochainRefinement A hLK =
      finiteCochainRefinement A (hLK.trans hKN) := by
  ext i
  apply DFunLike.ext _ _
  intro f
  funext x
  dsimp [finiteCochainRefinement, groupCohomology.cochainsMap]
  dsimp [inflationCoefficientMap]
  apply Subtype.ext
  change
    (f (openNormal hKN ∘
      (openNormal hLK ∘ x))).1 =
      (f (openNormal (hLK.trans hKN) ∘ x)).1
  apply congrArg (fun y ↦ (f y).1)
  funext j
  change openNormal hKN (openNormal hLK (x j)) =
    openNormal (hLK.trans hKN) (x j)
  refine QuotientGroup.induction_on (x j) ?_
  intro g
  rfl

/-- The finite-quotient inhomogeneous cochain complexes, organized as the
filtered chain-level diagram whose cohomology is Milne's system. -/
def finiteCochainDiagram (A : Rep ℤ G) :
    OpenInflationIndex G ⥤
      CochainComplex.{0, 1, 0} (ModuleCat.{0, 0} ℤ) ℕ where
  obj N := finiteQuotientCochains A (OrderDual.ofDual N)
  map {_ _} f := finiteCochainRefinement A
    (openInflationHom f)
  map_id N := cochain_refinement_refl A (OrderDual.ofDual N)
  map_comp {_ _ _} f g :=
    (cochain_refinement_trans A
      (openInflationHom g) (openInflationHom f)).symm

end

end Towers.CField.PCohom
