import Submission.ClassField.ProfiniteCohom.Cochains
import Submission.ClassField.CohomologyOps.Inflation

namespace Submission.CField.PCohom

open CategoryTheory

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]

abbrev underlyingRep
    (M : DiscreteContAction (TopModuleCat ℤ) G) : Rep ℤ G :=
  (Rep.ActionToRep ℤ G).obj
    (((CategoryTheory.forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).mapAction G).obj
      M.obj.obj)

abbrev OpenInflationIndex (G : Type) [Group G] [TopologicalSpace G] :=
  (OpenNormalSubgroup G)ᵒᵈ

def openInflationHom
    {N K : OpenInflationIndex G} (f : N ⟶ K) :
    OrderDual.ofDual K ≤ OrderDual.ofDual N :=
  leOfHom f

/-- The quotient homomorphism `G/K ⟶ G/N` for `K ≤ N`. -/
def openNormal {K N : OpenNormalSubgroup G} (hKN : K ≤ N) :
    G ⧸ (K : Subgroup G) →* G ⧸ (N : Subgroup G) :=
  QuotientGroup.map (K : Subgroup G) (N : Subgroup G) (MonoidHom.id G) hKN

@[simp]
theorem open_normal_mk {K N : OpenNormalSubgroup G} (hKN : K ≤ N) (g : G) :
    openNormal hKN (QuotientGroup.mk' (K : Subgroup G) g) =
      QuotientGroup.mk' (N : Subgroup G) g :=
  rfl

/-- If `K ≤ N`, inclusion `A^N ⊆ A^K` intertwines the action through
`G/K ⟶ G/N`. -/
def inflationCoefficientMap (A : Rep ℤ G)
    {K N : OpenNormalSubgroup G} (hKN : K ≤ N) :
    Rep.res (openNormal hKN)
        (A.quotientToInvariants (N : Subgroup G)) ⟶
      A.quotientToInvariants (K : Subgroup G) := by
  letI := A.hV2
  letI := (A.quotientToInvariants (N : Subgroup G)).hV2
  letI := (A.quotientToInvariants (K : Subgroup G)).hV2
  let i : Representation.invariants
        (A.ρ.comp (N : Subgroup G).subtype) →ₗ[ℤ]
      Representation.invariants (A.ρ.comp (K : Subgroup G).subtype) :=
    { toFun := fun x ↦ ⟨x.1, fun k ↦ x.2 ⟨k, hKN k.property⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Rep.ofHom ⟨i, fun q ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rfl⟩

/-- The finite-level inflation map associated to `K ≤ N`. -/
def finiteQuotientInflation (A : Rep ℤ G)
    {K N : OpenNormalSubgroup G} (hKN : K ≤ N) (r : ℕ) :
    groupCohomology (A.quotientToInvariants (N : Subgroup G)) r ⟶
      groupCohomology (A.quotientToInvariants (K : Subgroup G)) r :=
  groupCohomology.map (openNormal hKN)
    (inflationCoefficientMap A hKN) r

@[simp]
theorem finite_inflation_refl (A : Rep ℤ G)
    (N : OpenNormalSubgroup G) (r : ℕ) :
    finiteQuotientInflation A (show N ≤ N from le_rfl) r = 𝟙 _ := by
  let q := openNormal (show N ≤ N from le_rfl)
  let p : Rep.res q (A.quotientToInvariants (N : Subgroup G)) ⟶
      A.quotientToInvariants (N : Subgroup G) :=
    inflationCoefficientMap A (show N ≤ N from le_rfl)
  have hcochain : groupCohomology.cochainsMap q p =
      𝟙 (groupCohomology.inhomogeneousCochains
        (A.quotientToInvariants (N : Subgroup G))) := by
    ext i
    apply DFunLike.ext _ _
    intro f
    funext x
    dsimp [groupCohomology.cochainsMap]
    dsimp [p, inflationCoefficientMap]
    apply Subtype.ext
    change (f (q ∘ x)).1 = (f x).1
    apply congrArg (fun y ↦ (f y).1)
    funext j
    exact QuotientGroup.map_id_apply (N : Subgroup G) _ (x j)
  change HomologicalComplex.homologyMap (groupCohomology.cochainsMap q p) r = 𝟙 _
  rw [hcochain]
  exact HomologicalComplex.homologyMap_id _ r

theorem finite_inflation_trans (A : Rep ℤ G)
    {L K N : OpenNormalSubgroup G} (hLK : L ≤ K) (hKN : K ≤ N) (r : ℕ) :
    finiteQuotientInflation A hKN r ≫
        finiteQuotientInflation A hLK r =
      finiteQuotientInflation A (hLK.trans hKN) r := by
  let qNK := openNormal hKN
  let qLK := openNormal hLK
  let qNL := openNormal (hLK.trans hKN)
  let pNK : Rep.res qNK (A.quotientToInvariants (N : Subgroup G)) ⟶
      A.quotientToInvariants (K : Subgroup G) :=
    inflationCoefficientMap A hKN
  let pLK : Rep.res qLK (A.quotientToInvariants (K : Subgroup G)) ⟶
      A.quotientToInvariants (L : Subgroup G) :=
    inflationCoefficientMap A hLK
  let pNL : Rep.res qNL (A.quotientToInvariants (N : Subgroup G)) ⟶
      A.quotientToInvariants (L : Subgroup G) :=
    inflationCoefficientMap A (hLK.trans hKN)
  have hcochain :
      groupCohomology.cochainsMap qNK pNK ≫
          groupCohomology.cochainsMap qLK pLK =
        groupCohomology.cochainsMap qNL pNL := by
    ext i
    apply DFunLike.ext _ _
    intro f
    funext x
    dsimp [groupCohomology.cochainsMap]
    dsimp [pNK, pLK, pNL, inflationCoefficientMap]
    apply Subtype.ext
    change (f (qNK ∘ (qLK ∘ x))).1 = (f (qNL ∘ x)).1
    apply congrArg (fun y ↦ (f y).1)
    funext j
    change qNK (qLK (x j)) = qNL (x j)
    refine QuotientGroup.induction_on (x j) ?_
    intro g
    rfl
  change
    HomologicalComplex.homologyMap (groupCohomology.cochainsMap qNK pNK) r ≫
        HomologicalComplex.homologyMap (groupCohomology.cochainsMap qLK pLK) r =
      HomologicalComplex.homologyMap (groupCohomology.cochainsMap qNL pNL) r
  rw [← HomologicalComplex.homologyMap_comp, hcochain]

/-- The filtered system in Milne II.4.2. Its object at an open normal
subgroup `N` is `H^r(G/N, M^N)`, and its arrows are inflation maps as the
subgroups shrink. -/
def finiteCohomologyDiagram
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    OpenInflationIndex G ⥤ ModuleCat ℤ where
  obj N := groupCohomology
    ((underlyingRep M).quotientToInvariants
      ((OrderDual.ofDual N : OpenNormalSubgroup G) : Subgroup G)) r
  map {_ _} f := finiteQuotientInflation (underlyingRep M)
    (openInflationHom f) r
  map_id N := finite_inflation_refl (underlyingRep M)
    (OrderDual.ofDual N) r
  map_comp {_ _ _} f g :=
    (finite_inflation_trans (underlyingRep M)
      (openInflationHom g) (openInflationHom f) r).symm

end

end Submission.CField.PCohom
