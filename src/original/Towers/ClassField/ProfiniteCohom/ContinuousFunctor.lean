import Towers.ClassField.ProfiniteCohom.ContinuousCohomology
import Towers.ClassField.ProfiniteCohom.CochainFactorization

namespace Towers.CField.PCohom

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

def underlyingRepMap
    {M N : DiscreteContAction (TopModuleCat ℤ) G} (f : M ⟶ N) :
    underlyingRep M ⟶ underlyingRep N :=
  (Rep.ActionToRep ℤ G).map
    (((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).mapAction G).map f.hom.hom)

def continuousCochainAdd
    {M N : DiscreteContAction (TopModuleCat ℤ) G} (f : M ⟶ N) (r : ℕ) :
    AddCommGrpCat.of C(Fin r → G, M.obj.obj.V) ⟶
      AddCommGrpCat.of C(Fin r → G, N.obj.obj.V) :=
  AddCommGrpCat.ofHom
    { toFun := fun c ↦
        { toFun := fun x ↦ f.hom.hom.hom.hom (c x)
          continuous_toFun := f.hom.hom.hom.hom.continuous.comp c.continuous }
      map_zero' := by
        ext x
        exact map_zero f.hom.hom.hom.hom
      map_add' := fun c d ↦ by
        ext x
        exact map_add f.hom.hom.hom.hom (c x) (d x) }

def continuousCochainMap
    {M N : DiscreteContAction (TopModuleCat ℤ) G} (f : M ⟶ N) (r : ℕ) :
    continuousInhomogeneousCochains M r ⟶
      continuousInhomogeneousCochains N r :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).preimage
    (continuousCochainAdd f r)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem map_cochain_map
    {M N : DiscreteContAction (TopModuleCat ℤ) G} (f : M ⟶ N) (r : ℕ) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (continuousCochainMap f r) = continuousCochainAdd f r :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_preimage _

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem continuous_cochain
    {M N : DiscreteContAction (TopModuleCat ℤ) G} (f : M ⟶ N) (r : ℕ)
    (c : continuousInhomogeneousCochains M r) (x : Fin r → G) :
    continuousCochainMap f r c x = f.hom.hom.hom.hom (c x) := by
  have h := congrArg (fun φ ↦
    ((show C(Fin r → G, N.obj.obj.V) from φ c) x))
      (map_cochain_map f r)
  simpa [continuousCochainAdd] using h

def inhomogeneousCochainComplex
    {M N : DiscreteContAction (TopModuleCat ℤ) G} (f : M ⟶ N) :
    continuousInhomogeneousComplex M ⟶
      continuousInhomogeneousComplex N where
  f r := continuousCochainMap f r
  comm' i j hij := by
    subst j
    rw [show (continuousInhomogeneousComplex M).d i (i + 1) =
        continuousCochainDifferential M i from CochainComplex.of_d _ _ i]
    rw [show (continuousInhomogeneousComplex N).d i (i + 1) =
        continuousCochainDifferential N i from CochainComplex.of_d _ _ i]
    ext c
    apply ContinuousMap.ext
    intro x
    let c' : continuousInhomogeneousCochains M i := c
    change continuousCochainDifferential N i
        (continuousCochainMap f i c') x =
      continuousCochainMap f (i + 1)
        (continuousCochainDifferential M i c') x
    rw [continuous_cochain_differential N i (continuousCochainMap f i c') x]
    rw [continuous_cochain f (i + 1)
      (continuousCochainDifferential M i c') x]
    rw [continuous_cochain_differential M i c' x]
    simp_rw [continuous_cochain f i c']
    letI : Module ℤ (underlyingRep M) := (underlyingRep M).hV2
    letI : Module ℤ (underlyingRep N) := (underlyingRep N).hV2
    let p := (underlyingRepMap f).hom
    let a : underlyingRep M := c' fun q ↦ x q.succ
    let b : Fin (i + 1) → underlyingRep M :=
      fun q ↦ c' (q.contractNth (fun x₁ x₂ ↦ x₁ * x₂) x)
    have hact := Rep.hom_comm_apply (underlyingRepMap f) (x 0) a
    calc
      _ = p ((underlyingRep M).ρ (x 0) a) +
          ∑ q : Fin (i + 1),
            p ((underlyingRep M).hV2.smul ((-1 : ℤ) ^ ((q : ℕ) + 1)) (b q)) := by
        congr 1
        · exact hact.symm
        · apply Finset.sum_congr rfl
          intro q _
          exact (p.map_smul _ (b q)).symm
      _ = p ((underlyingRep M).ρ (x 0) a) +
          p (∑ q : Fin (i + 1),
            (underlyingRep M).hV2.smul ((-1 : ℤ) ^ ((q : ℕ) + 1)) (b q)) := by
        exact congrArg (fun y ↦
          p ((underlyingRep M).ρ (x 0) a) + y)
          (map_sum p (fun q : Fin (i + 1) ↦
            (underlyingRep M).hV2.smul
              ((-1 : ℤ) ^ ((q : ℕ) + 1)) (b q)) _).symm
      _ = _ := by
        simpa only [p, a, b, underlyingRepMap] using (map_add p _ _).symm

def inhomogeneousCochainFunctor :
    DiscreteContAction (TopModuleCat ℤ) G ⥤
      CochainComplex (ModuleCat ℤ) ℕ where
  obj M := continuousInhomogeneousComplex M
  map f := inhomogeneousCochainComplex f
  map_id M := by
    ext r c
    apply ContinuousMap.ext
    intro x
    change continuousCochainMap (𝟙 M) r
        (show continuousInhomogeneousCochains M r from c) x =
      (show C(Fin r → G, M.obj.obj.V) from c) x
    rw [continuous_cochain]
    rfl
  map_comp f g := by
    ext r c
    apply ContinuousMap.ext
    intro x
    change continuousCochainMap (f ≫ g) r
        (show continuousInhomogeneousCochains _ r from c) x =
      continuousCochainMap g r
        (continuousCochainMap f r
          (show continuousInhomogeneousCochains _ r from c)) x
    rw [continuous_cochain, continuous_cochain,
      continuous_cochain]
    rfl

end
end Towers.CField.PCohom
