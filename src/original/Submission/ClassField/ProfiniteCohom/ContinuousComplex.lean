import Submission.ClassField.ProfiniteCohom.ContinuousColimit
import Submission.ClassField.ProfiniteCohom.FilteredColimitExact

namespace Submission.CField.PCohom

open CategoryTheory CategoryTheory.Limits
open Submission.CField.COps.CPFuncto

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem continuous_contractNth (n : ℕ) (j : Fin (n + 1)) :
    Continuous (Fin.contractNth j (· * ·) :
      (Fin (n + 1) → G) → (Fin n → G)) := by
  apply continuous_pi
  intro k
  unfold Fin.contractNth
  split
  · exact continuous_apply _
  split
  · exact (continuous_apply _).mul (continuous_apply _)
  · exact continuous_apply _

def cochainDifferentialAdd
    (M : DiscreteContAction (TopModuleCat ℤ) G) (n : ℕ) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        (continuousInhomogeneousCochains M n) ⟶
      (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        (continuousInhomogeneousCochains M (n + 1)) := by
  letI : MulAction G M.obj.obj.V := Action.instMulAction M.obj.obj
  letI : ContinuousSMul G M.obj.obj.V := M.obj.property
  letI : IsTopologicalAddGroup M.obj.obj.V :=
    M.obj.obj.V.isTopologicalAddGroup
  letI : ContinuousAdd M.obj.obj.V :=
    M.obj.obj.V.isTopologicalAddGroup.toContinuousAdd
  exact AddCommGrpCat.ofHom
    { toFun := fun f ↦
        { toFun := fun g ↦ show M.obj.obj.V from
            (underlyingRep M).ρ (g 0) (f fun i ↦ g i.succ) +
              ∑ j : Fin (n + 1),
                (underlyingRep M).hV2.smul
                  ((-1 : ℤ) ^ ((j : ℕ) + 1))
                    (f (Fin.contractNth j (· * ·) g))
          continuous_toFun := by
            have hact : Continuous (fun g : Fin (n + 1) → G ↦
                (show M.obj.obj.V from
                  (underlyingRep M).ρ (g 0) (f fun i ↦ g i.succ))) := by
              have hrho : Continuous (fun p : G × M.obj.obj.V ↦
                    (show M.obj.obj.V from
                      (underlyingRep M).ρ p.1 p.2)) := M.obj.property.1
              have htail : Continuous (fun g : Fin (n + 1) → G ↦
                  fun i : Fin n ↦ g i.succ) :=
                continuous_pi fun i ↦ continuous_apply i.succ
              exact hrho.comp ((continuous_apply 0).prodMk
                (f.continuous.comp htail))
            have hsum : Continuous (fun g : Fin (n + 1) → G ↦
                (show M.obj.obj.V from
                ∑ j : Fin (n + 1), (underlyingRep M).hV2.smul
                  ((-1 : ℤ) ^ ((j : ℕ) + 1))
                    (f (Fin.contractNth j (· * ·) g)))) := by
              have hsum' : Continuous (fun g : Fin (n + 1) → G ↦
                  ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) •
                    f (Fin.contractNth j (· * ·) g)) := by
                apply continuous_finsetSum
                intro j _
                exact (f.continuous.comp (continuous_contractNth n j)).const_smul _
              exact hsum'.congr fun g ↦ by
                apply Finset.sum_congr rfl
                intro j _
                let z : ℤ := (-1 : ℤ) ^ ((j : ℕ) + 1)
                let x : M.obj.obj.V :=
                  f (Fin.contractNth j (· * ·) g)
                have hM := int_smul_eq_zsmul
                  (AddCommGroup.toIntModule M.obj.obj.V) z x
                have hA := int_smul_eq_zsmul (underlyingRep M).hV2 z
                  (show underlyingRep M from x)
                simpa [z, x] using hM.trans hA.symm
            exact M.obj.obj.V.isTopologicalAddGroup.continuous_add.comp
              (hact.prodMk hsum) }
      map_zero' := by
        apply ContinuousMap.ext
        intro g
        change (inhomogeneousCochains.d (underlyingRep M) n).hom
          (0 : (Fin n → G) → underlyingRep M) g = 0
        exact congrFun (map_zero
          (inhomogeneousCochains.d (underlyingRep M) n).hom) g
      map_add' := by
        intro f h
        apply ContinuousMap.ext
        intro g
        let f' : (Fin n → G) → underlyingRep M := fun x ↦ f x
        let h' : (Fin n → G) → underlyingRep M := fun x ↦ h x
        change (inhomogeneousCochains.d (underlyingRep M) n).hom
          (f' + h') g =
            (inhomogeneousCochains.d (underlyingRep M) n).hom f' g +
              (inhomogeneousCochains.d (underlyingRep M) n).hom h' g
        exact congrFun (map_add
          (inhomogeneousCochains.d (underlyingRep M) n).hom f' h') g }

def continuousCochainDifferential
    (M : DiscreteContAction (TopModuleCat ℤ) G) (n : ℕ) :
    continuousInhomogeneousCochains M n ⟶
      continuousInhomogeneousCochains M (n + 1) :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).preimage
    (cochainDifferentialAdd M n)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem cochain_differential
    (M : DiscreteContAction (TopModuleCat ℤ) G) (n : ℕ) :
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
        (continuousCochainDifferential M n) =
      cochainDifferentialAdd M n :=
  (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_preimage _

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp]
theorem continuous_cochain_differential
    (M : DiscreteContAction (TopModuleCat ℤ) G) (n : ℕ)
    (f : continuousInhomogeneousCochains M n) (g : Fin (n + 1) → G) :
    continuousCochainDifferential M n f g =
      (underlyingRep M).ρ (g 0) (f fun i ↦ g i.succ) +
        ∑ j : Fin (n + 1), (underlyingRep M).hV2.smul
          ((-1 : ℤ) ^ ((j : ℕ) + 1))
            (f (Fin.contractNth j (· * ·) g)) := by
  have h := (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_preimage
    (cochainDifferentialAdd M n)
  have h' := congrArg (fun φ ↦
    ((show C(Fin (n + 1) → G, M.obj.obj.V) from φ f) g)) h
  exact h'

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem cochain_differential_coe
    (M : DiscreteContAction (TopModuleCat ℤ) G) (n : ℕ)
    (f : continuousInhomogeneousCochains M n) :
    (fun g ↦ continuousCochainDifferential M n f g) =
      (inhomogeneousCochains.d (underlyingRep M) n).hom
        (fun x ↦ f x) := by
  funext g
  rw [continuous_cochain_differential]
  rfl

/-- The usual complex of continuous inhomogeneous cochains. -/
noncomputable def continuousInhomogeneousComplex
    (M : DiscreteContAction (TopModuleCat ℤ) G) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (continuousInhomogeneousCochains M)
    (continuousCochainDifferential M) fun n ↦ by
      apply (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_injective
      ext f
      apply ContinuousMap.ext
      intro g
      change continuousCochainDifferential M (n + 1)
        (continuousCochainDifferential M n f) g = 0
      have hcoe := cochain_differential_coe M (n + 1)
        (continuousCochainDifferential M n f)
      rw [congrFun hcoe g, cochain_differential_coe]
      let fc : C(Fin n → G, M.obj.obj.V) := f
      let f' : (Fin n → G) → underlyingRep M := fun x ↦ fc x
      have h := congrArg (fun φ ↦ φ f')
        (groupCohomology.inhomogeneousCochains.d_comp_d
          n (underlyingRep M))
      have hg := congrFun h g
      simpa only [ModuleCat.hom_comp, LinearMap.coe_comp,
        Function.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
        f', fc] using hg

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem level_continuous_d
    (M : DiscreteContAction (TopModuleCat ℤ) G)
    (N : OpenNormalSubgroup G) (n : ℕ) :
    inhomogeneousCochains.d
          ((underlyingRep M).quotientToInvariants (N : Subgroup G)) n ≫
        finiteLevelContinuous M (n + 1) N =
      finiteLevelContinuous M n N ≫
        continuousCochainDifferential M n := by
  apply (forget₂ (ModuleCat ℤ) AddCommGrpCat).map_injective
  simp only [Functor.map_comp]
  erw [level_continuous, cochain_differential]
  erw [level_continuous]
  ext f
  apply ContinuousMap.ext
  intro g
  simp only [AddCommGrpCat.comp_apply]
  change
    ((show C(Fin (n + 1) → G, M.obj.obj.V) from
      levelContinuousAdd M (n + 1) N
        ((inhomogeneousCochains.d
          ((underlyingRep M).quotientToInvariants (N : Subgroup G)) n).hom f)) g) =
      ((show C(Fin (n + 1) → G, M.obj.obj.V) from
        cochainDifferentialAdd M n
          (levelContinuousAdd M n N f)) g)
  dsimp [levelContinuousAdd, cochainDifferentialAdd]
  let q := QuotientGroup.mk' (N : Subgroup G)
  let p := inflationInvariantsInclusion (N : Subgroup G) (underlyingRep M)
  have hc : inhomogeneousCochains.d
          ((underlyingRep M).quotientToInvariants (N : Subgroup G)) n ≫
        (groupCohomology.cochainsMap q p).f (n + 1) =
      (groupCohomology.cochainsMap q p).f n ≫
        inhomogeneousCochains.d (underlyingRep M) n :=
    by
      rw [← groupCohomology.inhomogeneousCochains.d_def,
        ← groupCohomology.inhomogeneousCochains.d_def]
      exact ((groupCohomology.cochainsMap q p).comm n (n + 1)).symm
  have hc' := congrArg (fun φ ↦ φ f) hc
  have hc'' := congrFun hc' g
  simpa only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    groupCohomology.cochainsMap_f_hom, LinearMap.compLeft_apply,
    LinearMap.funLeft_apply,
    p, inflationInvariantsInclusion, q,
    inhomogeneousCochains.d_hom_apply] using hc''

end
end Submission.CField.PCohom
