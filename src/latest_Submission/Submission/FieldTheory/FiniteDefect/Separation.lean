import Submission.FieldTheory.FiniteDefect.Images


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open ONCompar

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The honest finite kernel-image quotient at depth `n` has kernel exactly the
`n`th Zassenhaus layer enlarged by the actual initial Koch kernel.
-/
lemma initial_koch_sup
    (n : ℕ) :
    (initialKochImage n).ker =
      (zassenhausOpenSubgroup n : Subgroup initialKochFree.Carrier) ⊔
        initialKochQuotient.ker := by
  rw [initialKochImage, ← MonoidHom.comap_ker,
    QuotientGroup.ker_mk']
  rw [kernelImage, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]

/--
Any map killing both the actual initial Koch kernel and the `n`th Zassenhaus
layer kills the honest finite kernel-image quotient kernel at depth `n`.
-/
lemma initial_koch_layer
    {P : Type}
    [Group P]
    (α : initialKochFree.Carrier →* P)
    (n : ℕ)
    (hLayer :
      (zassenhausOpenSubgroup n : Subgroup initialKochFree.Carrier) ≤
        α.ker)
    (hKoch : initialKochQuotient.ker ≤ α.ker) :
    (initialKochImage n).ker ≤ α.ker := by
  rw [initial_koch_sup]
  exact sup_le hLayer hKoch

/--
Remember the discrete topology on every honest finite kernel-image quotient.
-/
instance initial_topological_space
    (n : ℕ) :
    TopologicalSpace (InitialKochImage n) :=
  ⊥

/--
Every honest finite kernel-image quotient has its remembered discrete
topology.
-/
instance initial_discrete_topology
    (n : ℕ) :
    DiscreteTopology (InitialKochImage n) :=
  ⟨rfl⟩

/--
Every honest finite kernel-image quotient is Hausdorff for its remembered
discrete topology.
-/
instance initial_t_space
    (n : ℕ) :
    T2Space (InitialKochImage n) := by
  infer_instance

/--
The honest finite kernel-image quotient system object remembers the same
discrete topology as its named quotient level.
-/
instance obj_topological_space
    (n : ℕ) :
    TopologicalSpace (InitialKochSystem.obj n) := by
  change TopologicalSpace (InitialKochImage n)
  infer_instance

/--
The honest finite kernel-image quotient system object is Hausdorff for its
remembered discrete topology.
-/
instance obj_t_space
    (n : ℕ) :
    T2Space (InitialKochSystem.obj n) := by
  change T2Space (InitialKochImage n)
  infer_instance

/--
The honest finite kernel-image quotient tower remembers the discrete `T₂`
topology on every finite level.
-/
def InitialTopologicalSystem :
    Group.tSQuotie where
  toSystem := InitialKochSystem
  topologicalSpace_obj := fun _n => inferInstance
  objT2 := fun _n => inferInstance

/--
The honest finite kernel-image quotient factors are continuous.
-/
lemma initial_koch_continuous
    (n : ℕ) :
    Continuous (initialKochFactor n) := by
  apply initial_koch.continuous_iff.mpr
  change Continuous
    ((initialKochFactor n).comp
      initialKochQuotient)
  rw [initial_image_comp]
  change Continuous
    ((QuotientGroup.mk'
      (kernelImage initialKochQuotient
        (zassenhausOpenSubgroup n))).comp
      (openNormalLayer (zassenhausOpenSubgroup n)))
  have hkernelImageQuotientMapContinuous :
      Continuous
        (QuotientGroup.mk'
          (kernelImage initialKochQuotient
            (zassenhausOpenSubgroup n))) :=
    continuous_of_discreteTopology
  exact hkernelImageQuotientMapContinuous.comp
    (pro_open_continuous
      (zassenhausOpenSubgroup n))

/--
The honest finite kernel-image quotient comparison map is continuous.
-/
lemma initial_comparison_continuous :
    Continuous initialImageComparison := by
  exact Group.tSQuotie.inverse_lift_continuous
    InitialTopologicalSystem
    initialKochFactor
    initial_koch_continuous
    (fun hnm => initial_comp_factor hnm)

/--
Every coherent thread in the honest finite kernel-image quotient tower comes
from an element of the actual initial Galois group.
-/
lemma initial_comparison_surjective :
    Function.Surjective initialImageComparison := by
  exact Group.tSQuotie.limit_compact_space
    InitialTopologicalSystem
    initialKochFactor
    initial_koch_continuous
    initial_image_surjective
    (fun hnm => initial_comp_factor hnm)

/--
Pull a finite `3`-shadow of the actual initial Galois group back to the
initial free pro-`3` group.
-/
def initialShadowPullback
    (S : Shadow 3 initialGaloisGroup) :
    initialKochFree.Carrier →* S.Target :=
  S.map.comp initialKochQuotient

/--
The pullback of an actual finite `3`-shadow along the initial Koch quotient is
continuous.
-/
lemma shadow_pullback_continuous
    (S : Shadow 3 initialGaloisGroup) :
    Continuous (initialShadowPullback S) := by
  exact S.map_continuous.comp initial_quotient_continuous

/--
The actual initial Koch kernel lies in the kernel of every actual finite
shadow pullback.
-/
lemma initial_shadow_pullback
    (S : Shadow 3 initialGaloisGroup) :
    initialKochQuotient.ker ≤
      (initialShadowPullback S).ker := by
  intro x hx
  change S.map (initialKochQuotient x) = 1
  rw [MonoidHom.mem_ker.mp hx]
  exact S.map.map_one

/--
Every actual finite `3`-shadow pullback kills the displayed tame Koch
relators because the actual initial Koch quotient already kills them.
-/
lemma shadow_pullback_kills
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup) :
    ∀ i : Fin 5,
      initialShadowPullback S
          (initialTameRelator D.frobeniusLift i) = 1 := by
  intro i
  change S.map (initialKochQuotient
      (initialTameRelator D.frobeniusLift i)) = 1
  rw [D.tame_maps_one i]
  exact S.map.map_one

/--
The least canonical Zassenhaus depth through which one actual finite
`3`-shadow of the actual initial Galois group factors after pullback to the
initial free pro-`3` group.
-/
abbrev ShadowTargetDepth
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup) :=
  D.ThreeTargetDepth
    (initialShadowPullback S)
    (shadow_pullback_continuous S)
    S.target_p_group
    (D.shadow_pullback_kills S)

/--
At the canonical target depth of one actual finite `3`-shadow pullback, the
corresponding Zassenhaus layer lies inside the pullback kernel.
-/
lemma openTargetDepth
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup) :
    (zassenhausOpenSubgroup
        (D.ShadowTargetDepth S) :
      Subgroup initialKochFree.Carrier) ≤
      (initialShadowPullback S).ker := by
  exact D.relator_target_depth
    (initialShadowPullback S)
    (shadow_pullback_continuous S)
    S.target_p_group
    (D.shadow_pullback_kills S)

/--
Every depth at or beyond the canonical target depth of one actual finite
`3`-shadow pullback lies inside that pullback kernel.
-/
lemma open_normal_target
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup)
    {n : ℕ}
    (htarget : D.ShadowTargetDepth S ≤ n) :
    (zassenhausOpenSubgroup n : Subgroup initialKochFree.Carrier) ≤
      (initialShadowPullback S).ker := by
  exact D.open_target_depth
    (initialShadowPullback S)
    (shadow_pullback_continuous S)
    S.target_p_group
    (D.shadow_pullback_kills S)
    htarget

/--
At every depth beyond its canonical target depth, an actual finite
`3`-shadow pullback kills the honest finite kernel-image quotient kernel.
-/
lemma shadow_pullback_target
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup)
    {n : ℕ}
    (htarget : D.ShadowTargetDepth S ≤ n) :
    (initialKochImage n).ker ≤
      (initialShadowPullback S).ker := by
  apply initial_koch_layer
  · exact D.open_normal_target
      S htarget
  · exact initial_shadow_pullback S

/--
The factor from one sufficiently deep honest finite kernel-image quotient to
an actual finite `3`-shadow target.
-/
def shadowTargetDepth
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup)
    {n : ℕ}
    (htarget : D.ShadowTargetDepth S ≤ n) :
    InitialKochImage n →* S.Target :=
  PRFact.factorSurjective
    (initialKochImage n)
    (initialShadowPullback S)
    (koch_image_surjective n)
    (D.shadow_pullback_target
      S htarget)

/--
The sufficiently deep honest finite kernel-image quotient factor descends the
actual finite shadow pullback.
-/
lemma initial_shadow_target
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup)
    {n : ℕ}
    (htarget : D.ShadowTargetDepth S ≤ n) :
    (D.shadowTargetDepth S htarget).comp
        (initialKochImage n) =
      initialShadowPullback S := by
  exact PRFact.factor_map_of
    (initialKochImage n)
    (initialShadowPullback S)
    (koch_image_surjective n)
    (D.shadow_pullback_target
      S htarget)

/--
Every sufficiently deep honest finite kernel-image quotient factor descends the
actual finite shadow map from the actual initial Galois group.
-/
lemma shadow_target_comp
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup)
    {n : ℕ}
    (htarget : D.ShadowTargetDepth S ≤ n) :
    (D.shadowTargetDepth S htarget).comp
        (initialKochFactor n) =
      S.map := by
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hquotient := DFunLike.congr_fun
    (D.initial_shadow_target
      S htarget)
    x
  have hfactor := DFunLike.congr_fun
    (initial_image_comp n)
    x
  change D.shadowTargetDepth S htarget
      (initialKochImage n x) =
    initialShadowPullback S x at hquotient
  change initialKochFactor n (initialKochQuotient x) =
    initialKochImage n x at hfactor
  change D.shadowTargetDepth S htarget
      (initialKochFactor n (initialKochQuotient x)) =
    S.map (initialKochQuotient x)
  rw [hfactor]
  exact hquotient

/--
Every actual finite `3`-shadow of the actual initial Galois group factors
uniquely through every sufficiently deep honest finite kernel-image quotient.
-/
lemma uniquely_through_target
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup)
    {n : ℕ}
    (htarget : D.ShadowTargetDepth S ≤ n) :
    FactorsUniquelyThrough
      (initialKochFactor n)
      S.map := by
  apply factors_uniquely_ker
    (initialKochFactor n)
    S.map
    (initial_image_surjective n)
  apply ker_factors_through
    (initialKochFactor n)
    S.map
  exact ⟨D.shadowTargetDepth S htarget,
    D.shadow_target_comp S htarget⟩

/--
The canonical target-depth honest finite kernel-image quotient factor of one
actual finite `3`-shadow.
-/
def initialShadowTarget
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup) :
    InitialKochImage
        (D.ShadowTargetDepth S) →* S.Target :=
  D.shadowTargetDepth S le_rfl

/--
At its canonical target depth, an actual finite `3`-shadow factors through the
honest finite kernel-image quotient.
-/
lemma initial_shadow_comp
    (D : KRData)
    (S : Shadow 3 initialGaloisGroup) :
    (D.initialShadowTarget S).comp
        (initialKochFactor
          (D.ShadowTargetDepth S)) =
      S.map := by
  exact D.shadow_target_comp
    S le_rfl

/--
The honest finite kernel-image shadows along canonical Zassenhaus depths
separate every nonidentity element of the actual initial Galois group.
-/
lemma initial_shadow_ne
    (D : KRData)
    {y : initialGaloisGroup}
    (hy : y ≠ 1) :
    ∃ n : ℕ, (initialImageShadow n).map y ≠ 1 := by
  rcases (residually_separates_nontrivial 3 initialGaloisGroup).mp
      initial_galois_residually y hy with
    ⟨S, hS⟩
  refine ⟨D.ShadowTargetDepth S, ?_⟩
  intro hkernelImage
  apply hS
  have hfactor := DFunLike.congr_fun
    (D.initial_shadow_comp S)
    y
  change D.initialShadowTarget S
      ((initialImageShadow
        (D.ShadowTargetDepth S)).map y) =
    S.map y at hfactor
  rw [hkernelImage] at hfactor
  exact hfactor.symm.trans
    (D.initialShadowTarget S).map_one

/--
The actual initial Galois group injects into the inverse limit of its honest
finite kernel-image quotients along the canonical Zassenhaus depths.
-/
lemma initial_comparison_injective
    (D : KRData) :
    Function.Injective initialImageComparison := by
  apply (MonoidHom.ker_eq_bot_iff initialImageComparison).mp
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_bot]
    by_contra hyne
    rcases D.initial_shadow_ne hyne with
      ⟨n, hn⟩
    apply hn
    have hcoordinate := DFunLike.congr_fun
      (initial_comparison_coordinate n)
      y
    change Group.inverseLimitProjection InitialKochSystem n
        (initialImageComparison y) =
      initialKochFactor n y at hcoordinate
    change initialKochFactor n y = 1
    rw [← hcoordinate, MonoidHom.mem_ker.mp hy]
    exact map_one _
  · exact bot_le

/--
The actual initial Galois group is canonically the inverse limit of its honest
finite kernel-image quotients along the canonical Zassenhaus depths.
-/
def initialKochComparison
    (D : KRData) :
    initialGaloisGroup ≃* InitialKochLimit :=
  MulEquiv.ofBijective
    initialImageComparison
    ⟨D.initial_comparison_injective,
      initial_comparison_surjective⟩

/--
The honest finite kernel-image quotient comparison equivalence is induced by
the honest finite kernel-image quotient comparison map.
-/
lemma initial_comparison_monoid
    (D : KRData) :
    D.initialKochComparison.toMonoidHom =
      initialImageComparison := by
  rfl

/--
The actual initial Galois group is canonically continuously isomorphic to the
inverse limit of its honest finite kernel-image quotients.
-/
def initialComparisonContinuous
    (D : KRData) :
    initialGaloisGroup ≃ₜ* InitialKochLimit where
  toMulEquiv := D.initialKochComparison
  continuous_toFun := initial_comparison_continuous
  continuous_invFun := by
    have hcontinuous :
        Continuous D.initialKochComparison := by
      change Continuous initialImageComparison
      exact initial_comparison_continuous
    exact hcontinuous.continuous_symm_of_equiv_compact_to_t2

/--
Remember the discrete topology on every canonical finite defect quotient.
-/
instance defect_topological_space
    (D : KRData)
    (n : ℕ) :
    TopologicalSpace (D.CanonicalKochDefect n) :=
  ⊥

/--
Every canonical finite defect quotient has its remembered discrete topology.
-/
instance defect_discrete_topology
    (D : KRData)
    (n : ℕ) :
    DiscreteTopology (D.CanonicalKochDefect n) :=
  ⟨rfl⟩

/--
Every canonical finite defect quotient is Hausdorff for its remembered
discrete topology.
-/
instance defect_t_space
    (D : KRData)
    (n : ℕ) :
    T2Space (D.CanonicalKochDefect n) := by
  infer_instance

/--
The canonical finite defect quotient system object remembers the same
discrete topology as its named quotient level.
-/
instance defect_obj_space
    (D : KRData)
    (n : ℕ) :
    TopologicalSpace (D.CanonicalDefectSystem.obj n) := by
  change TopologicalSpace (D.CanonicalKochDefect n)
  infer_instance

/--
The canonical finite defect quotient system object is Hausdorff for its
remembered discrete topology.
-/
instance system_obj_t
    (D : KRData)
    (n : ℕ) :
    T2Space (D.CanonicalDefectSystem.obj n) := by
  change T2Space (D.CanonicalKochDefect n)
  infer_instance

/--
The canonical finite defect quotient tower remembers the discrete `T₂`
topology on every finite level.
-/
def DefectTopologicalSystem
    (D : KRData) :
    Group.tSQuotie where
  toSystem := D.CanonicalDefectSystem
  topologicalSpace_obj := fun _n => inferInstance
  objT2 := fun _n => inferInstance

/--
Canonical finite defect quotient factors are continuous.
-/
lemma canonical_defect_continuous
    (D : KRData)
    (n : ℕ) :
    Continuous (D.canonicalDefectFactor n) := by
  exact (D.kochDefectShadow n).map_continuous

/--
The canonical finite defect quotient comparison map is continuous.
-/
lemma defect_comparison_continuous
    (D : KRData) :
    Continuous D.kochDefectComparison := by
  exact Group.tSQuotie.inverse_lift_continuous
    D.DefectTopologicalSystem
    D.canonicalDefectFactor
    D.canonical_defect_continuous
    (fun hnm => D.canonical_defect_factor hnm)

/--
Every coherent thread in the canonical finite defect quotient tower comes from
an element of the actual initial Galois group.
-/
lemma canonical_comparison_surjective
    (D : KRData) :
    Function.Surjective D.kochDefectComparison := by
  exact Group.tSQuotie.limit_compact_space
    D.DefectTopologicalSystem
    D.canonicalDefectFactor
    D.canonical_defect_continuous
    D.canonical_defect_surjective
    (fun hnm => D.canonical_defect_factor hnm)

/--
The canonical finite defect shadows also separate every nonidentity element of
the actual initial Galois group.
-/
lemma defect_shadow_ne
    (D : KRData)
    {y : initialGaloisGroup}
    (hy : y ≠ 1) :
    ∃ n : ℕ, (D.kochDefectShadow n).map y ≠ 1 := by
  rcases D.initial_shadow_ne hy with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro hdefect
  apply hn
  apply MonoidHom.mem_ker.mp
  rw [← D.defect_shadow_image]
  exact MonoidHom.mem_ker.mpr hdefect

/--
Unconditionally, the actual initial Galois group injects into the inverse
limit of the canonical finite defect quotient shadows.
-/
lemma canonical_comparison_injective
    (D : KRData) :
    Function.Injective D.kochDefectComparison := by
  apply (MonoidHom.ker_eq_bot_iff D.kochDefectComparison).mp
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_bot]
    by_contra hyne
    rcases D.defect_shadow_ne hyne with
      ⟨n, hn⟩
    apply hn
    have hcoordinate := DFunLike.congr_fun
      (D.defect_comparison_coordinate n)
      y
    change Group.inverseLimitProjection D.CanonicalDefectSystem n
        (D.kochDefectComparison y) =
      D.canonicalDefectFactor n y at hcoordinate
    change D.canonicalDefectFactor n y = 1
    rw [← hcoordinate, MonoidHom.mem_ker.mp hy]
    exact map_one _
  · exact bot_le

/--
Unconditionally, the actual initial Galois group is canonically the inverse
limit of the canonical finite defect quotient shadows.
-/
def canonicalDefectComparison
    (D : KRData) :
    initialGaloisGroup ≃* Group.inverseLimit D.CanonicalDefectSystem :=
  MulEquiv.ofBijective
    D.kochDefectComparison
    ⟨D.canonical_comparison_injective,
      D.canonical_comparison_surjective⟩

/--
The canonical finite defect quotient comparison equivalence is induced by the
canonical finite defect quotient comparison map.
-/
lemma defect_comparison_monoid
    (D : KRData) :
    D.canonicalDefectComparison.toMonoidHom =
      D.kochDefectComparison := by
  rfl

/--
Unconditionally, the actual initial Galois group is canonically continuously
isomorphic to the inverse limit of the canonical finite defect quotient
shadows.
-/
def defectComparisonContinuous
    (D : KRData) :
    initialGaloisGroup ≃ₜ* Group.inverseLimit D.CanonicalDefectSystem where
  toMulEquiv := D.canonicalDefectComparison
  continuous_toFun := D.defect_comparison_continuous
  continuous_invFun := by
    have hcontinuous :
        Continuous D.canonicalDefectComparison := by
      change Continuous D.kochDefectComparison
      exact D.defect_comparison_continuous
    exact hcontinuous.continuous_symm_of_equiv_compact_to_t2

end KRData

end TBluepr
end Submission
