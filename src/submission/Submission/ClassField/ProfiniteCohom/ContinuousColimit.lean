import Submission.ClassField.ProfiniteCohom.CochainComplex
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Topology.ContinuousMap.Algebra

namespace Submission.CField.PCohom

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Continuous inhomogeneous cochains in degree `r`. -/
abbrev continuousInhomogeneousCochains
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ C(Fin r → G, M.obj.obj.V)

/-- The degree-`r` module diagram underlying the finite-quotient cochain
complex diagram. -/
abbrev cochainModuleDiagram
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    OpenInflationIndex G ⥤ ModuleCat ℤ :=
  finiteCochainDiagram (underlyingRep M) ⋙
    HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) r

/-- The underlying additive map inflating a finite-level cochain to a
continuous cochain on `G`. -/
def levelContinuousAdd (M : DiscreteContAction (TopModuleCat ℤ) G)
    (r : ℕ) (N : OpenNormalSubgroup G) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        ((finiteQuotientCochains (underlyingRep M) N).X r) ⟶
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        (continuousInhomogeneousCochains M r) :=
  AddCommGrpCat.ofHom
    { toFun := fun f ↦
        { toFun := fun x ↦ (f (fun i ↦
            QuotientGroup.mk' (N : Subgroup G) (x i))).1
          continuous_toFun := by
            have hf : Continuous (fun q : Fin r → G ⧸ (N : Subgroup G) ↦
                (show M.obj.obj.V from (f q).1)) :=
              continuous_of_discreteTopology
            exact hf.comp (continuous_pi fun i ↦
              continuous_quotient_mk'.comp (continuous_apply i)) }
      map_zero' := by ext; rfl
      map_add' := by intro f g; ext; rfl }

/-- Inflation of a finite-level cochain to a continuous cochain on `G`, as
a `ℤ`-linear map. -/
def finiteLevelContinuous (M : DiscreteContAction (TopModuleCat ℤ) G)
    (r : ℕ) (N : OpenNormalSubgroup G) :
    (finiteQuotientCochains (underlyingRep M) N).X r ⟶
      continuousInhomogeneousCochains M r :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).preimage
    (levelContinuousAdd M r N)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem level_continuous
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ)
    (N : OpenNormalSubgroup G) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (finiteLevelContinuous M r N) =
      levelContinuousAdd M r N :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_preimage _

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem finite_level_continuous
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ)
    (N : OpenNormalSubgroup G)
    (f : (finiteQuotientCochains (underlyingRep M) N).X r) (x : Fin r → G) :
    finiteLevelContinuous M r N f x =
      (f (fun i ↦ QuotientGroup.mk' (N : Subgroup G) (x i))).1 :=
  by
    have h := congrArg (fun φ ↦
      ((show C(Fin r → G, M.obj.obj.V) from φ f) x))
      (level_continuous M r N)
    exact h

/-- The finite-level inflations form a cocone on the degree-`r` diagram. -/
def levelContinuousCocone
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    Cocone (cochainModuleDiagram M r) where
  pt := continuousInhomogeneousCochains M r
  ι :=
    { app := fun N ↦ finiteLevelContinuous M r (OrderDual.ofDual N)
      naturality := fun N K f ↦ by
        apply (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_injective
        simp only [Functor.map_comp, Functor.const_obj_map]
        erw [level_continuous, level_continuous]
        ext c
        apply ContinuousMap.ext
        intro x
        simp only [ConcreteCategory.comp_apply]
        change
          (c (fun i ↦ openNormal
            (openInflationHom f)
              (QuotientGroup.mk'
                ((show OpenNormalSubgroup G from OrderDual.ofDual K) : Subgroup G)
                (x i)))).1 =
            (c (fun i ↦
              QuotientGroup.mk'
                ((show OpenNormalSubgroup G from OrderDual.ofDual N) : Subgroup G)
                (x i))).1
        rfl }

/-- The canonical map from the algebraic filtered colimit of finite-level
cochains to continuous cochains. -/
def levelColimitContinuous
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    colimit (cochainModuleDiagram M r) ⟶
      continuousInhomogeneousCochains M r :=
  colimit.desc _ (levelContinuousCocone M r)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem level_colimit_continuousι
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ)
    (N : OpenNormalSubgroup G)
    (f : (finiteQuotientCochains (underlyingRep M) N).X r) :
    levelColimitContinuous M r
        (colimit.ι (cochainModuleDiagram M r)
          (OrderDual.toDual N) f) =
      finiteLevelContinuous M r N f := by
  rw [← ConcreteCategory.comp_apply]
  exact congrArg (fun φ ↦ φ f)
    (colimit.ι_desc (levelContinuousCocone M r)
      (OrderDual.toDual N))

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Specialized common-refinement criterion for representation-valued
finite quotient cochains. -/
theorem rep_cochains_inf (A : Rep ℤ G) (r : ℕ)
    {N K : OpenNormalSubgroup G}
    (f : (finiteQuotientCochains A N).X r)
    (g : (finiteQuotientCochains A K).X r)
    (h : ∀ x : Fin r → G,
      (f (fun i ↦ QuotientGroup.mk' (N : Subgroup G) (x i))).1 =
        (g (fun i ↦ QuotientGroup.mk' (K : Subgroup G) (x i))).1) :
    (finiteCochainRefinement A
      (show N ⊓ K ≤ N from inf_le_left)).f r f =
      (finiteCochainRefinement A
        (show N ⊓ K ≤ K from inf_le_right)).f r g := by
  ext x
  choose y hy using fun i ↦ QuotientGroup.mk_surjective (x i)
  have hxy : (fun i ↦ QuotientGroup.mk'
      ((N ⊓ K : OpenNormalSubgroup G) : Subgroup G) (y i)) = x := by
    funext i
    exact hy i
  subst x
  exact h y

theorem level_colimit_surjective
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    Function.Surjective (levelColimitContinuous M r) := by
  intro c
  letI : MulAction G M.obj.obj.V := Action.instMulAction M.obj.obj
  letI : ContinuousSMul G M.obj.obj.V := M.obj.property
  letI : DiscreteTopology M.obj.obj.V := M.property
  obtain ⟨N, fN, hfN⟩ := cochain_descends_points
    (G := G) (X := M.obj.obj.V) r c c.continuous
  let j : OpenInflationIndex G := OrderDual.toDual N
  let F := cochainModuleDiagram M r
  refine ⟨colimit.ι F j fN, ?_⟩
  have hι : colimit.ι F j ≫ levelColimitContinuous M r =
      finiteLevelContinuous M r N := by
    dsimp [F, j, levelColimitContinuous]
    exact colimit.ι_desc (levelContinuousCocone M r)
      (OrderDual.toDual N)
  rw [← ConcreteCategory.comp_apply, hι]
  apply ContinuousMap.ext
  intro x
  have hmap := congrArg (fun φ ↦
      ((show C(Fin r → G, M.obj.obj.V) from φ fN) x))
    (level_continuous M r N)
  change ((show C(Fin r → G, M.obj.obj.V) from
    ((forget₂ (ModuleCat ℤ) AddCommGrpCat).map
      (finiteLevelContinuous M r N)) fN) x) = c x
  exact hmap.trans (hfN x)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem level_colimit_injective
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    Function.Injective (levelColimitContinuous M r) := by
  intro x y hxy
  let F := cochainModuleDiagram M r
  let U := forget (ModuleCat ℤ)
  have hc : IsColimit (U.mapCocone (colimit.cocone F)) :=
    isColimitOfPreserves U (colimit.isColimit F)
  obtain ⟨i, xi, hxi⟩ := Types.jointly_surjective_of_isColimit hc x
  obtain ⟨j, yj, hyj⟩ := Types.jointly_surjective_of_isColimit hc y
  subst x
  subst y
  let N : OpenNormalSubgroup G := OrderDual.ofDual i
  let K : OpenNormalSubgroup G := OrderDual.ofDual j
  have hcont : finiteLevelContinuous M r N xi =
      finiteLevelContinuous M r K yj := by
    change levelColimitContinuous M r (colimit.ι F i xi) =
      levelColimitContinuous M r (colimit.ι F j yj) at hxy
    erw [level_colimit_continuousι,
      level_colimit_continuousι] at hxy
    exact hxy
  have hpoint : ∀ z : Fin r → G,
      (xi (fun a ↦ QuotientGroup.mk' (N : Subgroup G) (z a))).1 =
        (yj (fun a ↦ QuotientGroup.mk' (K : Subgroup G) (z a))).1 := by
    intro z
    have hz := congrArg (fun q : C(Fin r → G, M.obj.obj.V) ↦ q z) hcont
    have hzN : finiteLevelContinuous M r N xi z =
        (show M.obj.obj.V from
          (xi (fun a ↦ QuotientGroup.mk' (N : Subgroup G) (z a))).1) :=
      finite_level_continuous M r N xi z
    have hzK : finiteLevelContinuous M r K yj z =
        (show M.obj.obj.V from
          (yj (fun a ↦ QuotientGroup.mk' (K : Subgroup G) (z a))).1) :=
      finite_level_continuous M r K yj z
    exact hzN.symm.trans (hz.trans hzK)
  have href := rep_cochains_inf
    (underlyingRep M) r xi yj hpoint
  let L : OpenNormalSubgroup G := N ⊓ K
  let l : OpenInflationIndex G := OrderDual.toDual L
  let fi : i ⟶ l := homOfLE (by
    change L ≤ N
    exact inf_le_left)
  let fj : j ⟶ l := homOfLE (by
    change L ≤ K
    exact inf_le_right)
  have href' : F.map fi xi = F.map fj yj := by
    change
      (finiteCochainRefinement (underlyingRep M)
        (show L ≤ N from inf_le_left)).f r xi =
      (finiteCochainRefinement (underlyingRep M)
        (show L ≤ K from inf_le_right)).f r yj
    exact href
  have hfi : colimit.ι F i xi = colimit.ι F l (F.map fi xi) := by
    have hw0 : F.map fi ≫ colimit.ι F l = colimit.ι F i :=
      (colimit.cocone F).w fi
    have hw := congrArg (fun φ ↦ (ConcreteCategory.hom φ) xi) hw0
    simpa only [ConcreteCategory.comp_apply] using hw.symm
  have hfj : colimit.ι F j yj = colimit.ι F l (F.map fj yj) := by
    have hw0 : F.map fj ≫ colimit.ι F l = colimit.ι F j :=
      (colimit.cocone F).w fj
    have hw := congrArg (fun φ ↦ (ConcreteCategory.hom φ) yj) hw0
    simpa only [ConcreteCategory.comp_apply] using hw.symm
  exact hfi.trans ((congrArg (fun z ↦ colimit.ι F l z) href').trans hfj.symm)

noncomputable instance level_colimit_iso
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    IsIso (levelColimitContinuous M r) :=
  (ConcreteCategory.isIso_iff_bijective
    (levelColimitContinuous M r)).2
      ⟨level_colimit_injective M r,
        level_colimit_surjective M r⟩

/-- Degreewise form of Milne II.4.2: the filtered colimit of
`C^r(G/N, M^N)` is canonically isomorphic to the module of continuous
inhomogeneous `r`-cochains on `G`. -/
noncomputable def levelColimitIso
    (M : DiscreteContAction (TopModuleCat ℤ) G) (r : ℕ) :
    colimit (cochainModuleDiagram M r) ≅
      continuousInhomogeneousCochains M r :=
  asIso (levelColimitContinuous M r)

end

end Submission.CField.PCohom
