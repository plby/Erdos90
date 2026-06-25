import Submission.FieldTheory.FiniteDefect.Quotients
import Submission.FieldTheory.QuotientKoch.LayerWordImages


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PRFact
open ONCompar
open PCShadow

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
The actual initial Koch finite quotient visible after killing both the `n`th
Zassenhaus layer and the image of the actual initial Koch kernel in that
finite layer.
-/
abbrev InitialKochImage
    (n : ℕ) :=
  KernelImageQuotient initialKochQuotient
    (zassenhausOpenSubgroup n)

/--
The ambient map from the initial free pro-`3` group to its `n`th actual finite
kernel-image quotient.
-/
def initialKochImage
    (n : ℕ) :
    initialKochFree.Carrier →* InitialKochImage n :=
  (QuotientGroup.mk'
      (kernelImage initialKochQuotient
        (zassenhausOpenSubgroup n))).comp
    (openNormalLayer (zassenhausOpenSubgroup n))

/--
The actual initial Koch kernel dies in every actual finite kernel-image
quotient.
-/
lemma initial_koch_image
    (n : ℕ) :
    initialKochQuotient.ker ≤
      (initialKochImage n).ker := by
  intro x hx
  change QuotientGroup.mk'
      (kernelImage initialKochQuotient
        (zassenhausOpenSubgroup n))
      (openNormalLayer (zassenhausOpenSubgroup n) x) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨x, hx, rfl⟩

/--
The actual finite kernel-image quotient map is onto.
-/
lemma koch_image_surjective
    (n : ℕ) :
    Function.Surjective (initialKochImage n) := by
  exact (QuotientGroup.mk'_surjective
      (kernelImage initialKochQuotient
        (zassenhausOpenSubgroup n))).comp
    (QuotientGroup.mk'_surjective (zassenhausOpenSubgroup n : Subgroup
      initialKochFree.Carrier))

/--
The actual initial Galois group maps canonically onto the `n`th actual finite
kernel-image quotient.
-/
def initialKochFactor
    (n : ℕ) :
    initialGaloisGroup →* InitialKochImage n :=
  PRFact.factorSurjective
    initialKochQuotient
    (initialKochImage n)
    initial_quotient_surjective
    (initial_koch_image n)

/--
The actual finite kernel-image quotient factor descends its ambient quotient
map from the initial free pro-`3` group.
-/
lemma initial_image_comp
    (n : ℕ) :
    (initialKochFactor n).comp
        initialKochQuotient =
      initialKochImage n := by
  exact PRFact.factor_map_of
    initialKochQuotient
    (initialKochImage n)
    initial_quotient_surjective
    (initial_koch_image n)

/--
The actual finite kernel-image quotient factor is onto.
-/
lemma initial_image_surjective
    (n : ℕ) :
    Function.Surjective (initialKochFactor n) := by
  intro y
  rcases koch_image_surjective n y with ⟨x, rfl⟩
  exact ⟨initialKochQuotient x, by
    simpa using congrArg
      (fun ψ : initialKochFree.Carrier →* InitialKochImage n =>
        ψ x)
      (initial_image_comp n)⟩

/--
Every actual finite kernel-image quotient is an unconditional continuous
finite `3`-shadow of the actual initial Galois group.
-/
def initialImageShadow
    (n : ℕ) :
    Shadow 3 initialGaloisGroup := by
  letI : TopologicalSpace (InitialKochImage n) := ⊥
  letI : DiscreteTopology (InitialKochImage n) := ⟨rfl⟩
  letI : DiscreteTopology (OpenNormalLayer (zassenhausOpenSubgroup n)) :=
    pro_discrete_topology (zassenhausOpenSubgroup n)
  letI : Finite (OpenNormalLayer (zassenhausOpenSubgroup n)) :=
    pro_p_open (zassenhausOpenSubgroup n)
  letI : Finite (InitialKochImage n) :=
    Finite.of_surjective
      (QuotientGroup.mk'
        (kernelImage initialKochQuotient
          (zassenhausOpenSubgroup n)))
      (QuotientGroup.mk'_surjective
        (kernelImage initialKochQuotient
          (zassenhausOpenSubgroup n)))
  exact {
    Target := InitialKochImage n
    map := initialKochFactor n
    map_continuous := by
      apply initial_koch.continuous_iff.mpr
      change Continuous
        ((initialKochFactor n).comp initialKochQuotient)
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
    target_p_group :=
      (initialKochFree.isProP (zassenhausOpenSubgroup n)).of_surjective
        (QuotientGroup.mk'
          (kernelImage initialKochQuotient
            (zassenhausOpenSubgroup n)))
        (QuotientGroup.mk'_surjective
          (kernelImage initialKochQuotient
            (zassenhausOpenSubgroup n)))
  }

/--
Actual finite kernel-image shadows are quotient shadows of the actual initial
Galois group.
-/
lemma initial_shadow_surjective
    (n : ℕ) :
    Function.Surjective (initialImageShadow n).map := by
  exact initial_image_surjective n

/--
Deeper actual finite kernel-image quotient maps have smaller kernels.
-/
lemma initial_image_quotient
    {n m : ℕ}
    (hnm : n ≤ m) :
    (initialKochImage m).ker ≤
      (initialKochImage n).ker := by
  intro x hx
  change QuotientGroup.mk'
      (kernelImage initialKochQuotient
        (zassenhausOpenSubgroup n))
      (openNormalLayer (zassenhausOpenSubgroup n) x) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  change QuotientGroup.mk'
      (kernelImage initialKochQuotient
        (zassenhausOpenSubgroup m))
      (openNormalLayer (zassenhausOpenSubgroup m) x) = 1 at hx
  rcases (QuotientGroup.eq_one_iff _).mp hx with ⟨y, hy, hyx⟩
  exact ⟨y, hy, ONCofina.of_eq_le
    (OCTower.zassenhaus_open_normal
      initialKochFree.isProP
      initialKochFree.generator
      initialKochFree.dense_generator
      hnm)
    hyx⟩

/--
The canonical transition from the deeper `m`th actual finite kernel-image
quotient to the shallower `n`th one.
-/
def initialKochTransition
    {n m : ℕ}
    (hnm : n ≤ m) :
    InitialKochImage m →*
      InitialKochImage n :=
  PRFact.factorSurjective
    (initialKochImage m)
    (initialKochImage n)
    (koch_image_surjective m)
    (initial_image_quotient hnm)

/--
Actual finite kernel-image quotient transitions commute with the ambient
quotient maps.
-/
lemma initial_koch_comp
    {n m : ℕ}
    (hnm : n ≤ m) :
    (initialKochTransition hnm).comp
        (initialKochImage m) =
      initialKochImage n := by
  exact PRFact.factor_map_of
    (initialKochImage m)
    (initialKochImage n)
    (koch_image_surjective m)
    (initial_image_quotient hnm)

/--
Actual finite kernel-image quotient transitions send the class of every
ambient element to its class in the shallower quotient.
-/
lemma initial_koch_transition
    {n m : ℕ}
    (hnm : n ≤ m)
    (x : initialKochFree.Carrier) :
    initialKochTransition hnm
        (initialKochImage m x) =
      initialKochImage n x := by
  exact DFunLike.congr_fun
    (initial_koch_comp hnm)
    x

/--
Actual finite kernel-image quotient transitions are surjective.
-/
lemma initial_koch_surjective
    {n m : ℕ}
    (hnm : n ≤ m) :
    Function.Surjective (initialKochTransition hnm) := by
  intro y
  rcases koch_image_surjective n y with ⟨x, rfl⟩
  exact ⟨initialKochImage m x,
    initial_koch_transition hnm x⟩

/--
Actual finite kernel-image quotient transitions are the unique maps commuting
with the ambient quotient maps.
-/
lemma initial_koch_unique
    {n m : ℕ}
    (hnm : n ≤ m)
    (β : InitialKochImage m →*
      InitialKochImage n)
    (hβ : β.comp (initialKochImage m) =
      initialKochImage n) :
    β = initialKochTransition hnm := by
  apply MonoidHom.ext
  intro y
  rcases koch_image_surjective m y with ⟨x, rfl⟩
  exact (DFunLike.congr_fun hβ x).trans
    (initial_koch_transition hnm x).symm

/--
Actual finite kernel-image quotient transitions compose along increasing
Zassenhaus depths.
-/
lemma initial_transition_comp
    {n m k : ℕ}
    (hnm : n ≤ m)
    (hmk : m ≤ k) :
    (initialKochTransition hnm).comp
        (initialKochTransition hmk) =
      initialKochTransition (hnm.trans hmk) := by
  apply initial_koch_unique (hnm.trans hmk)
  rw [MonoidHom.comp_assoc,
    initial_koch_comp,
    initial_koch_comp]

/--
The actual finite kernel-image quotient transition at one depth is the
identity.
-/
lemma initial_koch_refl
    (n : ℕ) :
    initialKochTransition (Nat.le_refl n) =
      MonoidHom.id (InitialKochImage n) := by
  symm
  apply initial_koch_unique (Nat.le_refl n)
  rfl

/--
Actual finite kernel-image quotient factors from the actual initial Galois
group are compatible with actual finite kernel-image quotient transitions.
-/
lemma initial_comp_factor
    {n m : ℕ}
    (hnm : n ≤ m) :
    (initialKochTransition hnm).comp
        (initialKochFactor m) =
      initialKochFactor n := by
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hm := DFunLike.congr_fun
    (initial_image_comp m)
    x
  have hn := DFunLike.congr_fun
    (initial_image_comp n)
    x
  change initialKochFactor m (initialKochQuotient x) =
    initialKochImage m x at hm
  change initialKochFactor n (initialKochQuotient x) =
    initialKochImage n x at hn
  change initialKochTransition hnm
      (initialKochFactor m (initialKochQuotient x)) =
    initialKochFactor n (initialKochQuotient x)
  rw [hm, hn]
  exact initial_koch_transition hnm x

/--
The compatible inverse system of actual finite kernel-image quotients of the
actual initial Koch quotient.
-/
def InitialKochSystem :
    Group.cSQuotie where
  obj := InitialKochImage
  group_obj := fun _n => inferInstance
  finite_obj := fun n => by
    letI : Finite (OpenNormalLayer (zassenhausOpenSubgroup n)) :=
      pro_p_open (zassenhausOpenSubgroup n)
    exact Finite.of_surjective
      (QuotientGroup.mk'
        (kernelImage initialKochQuotient
          (zassenhausOpenSubgroup n)))
      (QuotientGroup.mk'_surjective
        (kernelImage initialKochQuotient
          (zassenhausOpenSubgroup n)))
  map := fun hmn => initialKochTransition hmn
  map_surjective := fun hmn =>
    initial_koch_surjective hmn
  map_id := initial_koch_refl
  map_comp := fun {_k _m _n} hkm hmn =>
    initial_transition_comp hkm hmn

/--
The inverse limit of the actual finite kernel-image quotient tower.
-/
abbrev InitialKochLimit :=
  Group.inverseLimit InitialKochSystem

/--
The actual initial Galois group maps canonically to the inverse limit of its
actual finite kernel-image quotients.
-/
def initialImageComparison :
    initialGaloisGroup →* InitialKochLimit :=
  Group.inverseLimitLift
    InitialKochSystem
    initialKochFactor
    (fun hnm => initial_comp_factor hnm)

/--
The coordinates of the actual finite kernel-image quotient comparison map are
the actual finite kernel-image quotient factors.
-/
lemma initial_comparison_coordinate
    (n : ℕ) :
    (Group.inverseLimitProjection InitialKochSystem n).comp
        initialImageComparison =
      initialKochFactor n := by
  exact Group.limit_projection_lift
    InitialKochSystem
    initialKochFactor
    (fun hnm => initial_comp_factor hnm)
    n

/--
An actual initial Galois element dies in the actual finite kernel-image
quotient inverse limit exactly when it dies in every actual finite
kernel-image quotient.
-/
lemma initial_koch_comparison
    (y : initialGaloisGroup) :
    y ∈ initialImageComparison.ker ↔
      ∀ n : ℕ, y ∈ (initialKochFactor n).ker := by
  constructor
  · intro hy n
    change initialKochFactor n y = 1
    rw [← initial_comparison_coordinate n]
    change Group.inverseLimitProjection InitialKochSystem n
      (initialImageComparison y) = 1
    rw [show initialImageComparison y = 1 from hy]
    exact map_one _
  · intro hy
    change initialImageComparison y = 1
    apply Subtype.ext
    funext n
    exact hy n

/--
The finite defect subgroup in one canonical relator quotient is exactly the
image of the actual initial Koch kernel in that canonical quotient.
-/
lemma koch_defect_quotient
    (D : KRData)
    (n : ℕ) :
    D.CanonicalDefectSubgroup n =
      initialKochQuotient.ker.map
        (D.ZassenhausRelatorQuotient n).map := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases D.zassenhaus_relator_surjective z with
      ⟨x, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · change initialKochQuotient x = 1
      have hdescent := congrArg
        (fun ψ : initialKochFree.Carrier →* initialGaloisGroup => ψ x)
        D.limit_descent_comp
      change D.inverseLimitDescent
          (D.zassenhausRelatorCompletion x) =
        initialKochQuotient x at hdescent
      rw [← hdescent]
      exact MonoidHom.mem_ker.mp hz
    · have hcoordinate := congrArg
        (fun ψ : initialKochFree.Carrier →*
            D.ZassenhausRelatorSystem.obj n =>
          ψ x)
        (D.zassenhaus_relator_coordinate n)
      exact hcoordinate.symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨D.zassenhausRelatorCompletion x, ?_, ?_⟩
    · change D.inverseLimitDescent
        (D.zassenhausRelatorCompletion x) = 1
      have hdescent := congrArg
        (fun ψ : initialKochFree.Carrier →* initialGaloisGroup => ψ x)
        D.limit_descent_comp
      change D.inverseLimitDescent
          (D.zassenhausRelatorCompletion x) =
        initialKochQuotient x at hdescent
      rw [hdescent]
      exact MonoidHom.mem_ker.mp hx
    · have hcoordinate := congrArg
        (fun ψ : initialKochFree.Carrier →*
            D.ZassenhausRelatorSystem.obj n =>
          ψ x)
        (D.zassenhaus_relator_coordinate n)
      exact hcoordinate

/--
The finite defect subgroup is the kernel of the canonical comparison from the
relator quotient of one Zassenhaus layer to the quotient by the actual Koch
kernel image in that layer.
-/
lemma defect_image_comparison
    (D : KRData)
    (n : ℕ) :
    D.CanonicalDefectSubgroup n =
      (D.relatorImageComparison n).ker := by
  rw [D.koch_defect_quotient]
  rw [ONCompar.relator_image_comparison]
  rw [kernelImage]
  rw [Subgroup.map_map]
  rfl

/--
The old relator-vs-kernel image comparison is the canonical relator quotient
map followed by the actual finite kernel-image quotient map.
-/
lemma image_comparison_comp
    (D : KRData)
    (n : ℕ) :
    (D.relatorImageComparison n).comp
        (D.ZassenhausRelatorQuotient n).map =
      initialKochImage n := by
  apply MonoidHom.ext
  intro x
  rfl

/--
The unconditional canonical finite defect quotient factor descends the
ambient initial Koch quotient to the finite defect quotient of the canonical
relator layer.
-/
lemma canonical_defect_comp
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectFactor n).comp
        initialKochQuotient =
      (D.canonicalKochDefect n).comp
        (D.ZassenhausRelatorQuotient n).map := by
  rw [← D.limit_descent_comp,
    ← MonoidHom.comp_assoc,
    D.defect_comp_descent,
    Group.cSQuotie.finiteDefectProjection,
    MonoidHom.comp_assoc,
    D.zassenhaus_relator_coordinate]
  rfl

/--
The finite defect quotient map is the universal quotient of the canonical
relator layer that kills the actual initial Koch kernel image in that layer.
-/
lemma koch_defect_comparison
    (D : KRData)
    (n : ℕ) :
    (D.canonicalKochDefect n).ker =
      (D.relatorImageComparison n).ker := by
  rw [canonicalKochDefect,
    Group.cSQuotie.defectQuotient]
  rw [(D.ZassenhausRelatorSystem.defectNormalSubgroup
    D.inverseLimitDescent
    D.limit_projection_surjective n).ker_projection]
  exact D.defect_image_comparison n

/--
The canonical finite defect quotient map is onto.
-/
lemma koch_defect_surjective
    (D : KRData)
    (n : ℕ) :
    Function.Surjective (D.canonicalKochDefect n) := by
  exact (D.ZassenhausRelatorSystem.defectNormalSubgroup
    D.inverseLimitDescent
    D.limit_projection_surjective n).projection_surjective

/--
The canonical finite defect quotient is the universal quotient of the
canonical relator layer through which the older relator-vs-kernel image
comparison factors.
-/
def defectComparisonFactor
    (D : KRData)
    (n : ℕ) :
    D.CanonicalKochDefect n →*
      InitialKochImage n :=
  PRFact.factorSurjective
    (D.canonicalKochDefect n)
    (D.relatorImageComparison n)
    (D.koch_defect_surjective n)
    (D.koch_defect_comparison
      n).le

/--
The finite defect quotient comparison factor descends the older
relator-vs-kernel image comparison.
-/
lemma defect_comparison_comp
    (D : KRData)
    (n : ℕ) :
    (D.defectComparisonFactor n).comp
        (D.canonicalKochDefect n) =
      D.relatorImageComparison n := by
  exact PRFact.factor_map_of
    (D.canonicalKochDefect n)
    (D.relatorImageComparison n)
    (D.koch_defect_surjective n)
    (D.koch_defect_comparison
      n).le

/--
The canonical finite defect quotient comparison factor is onto.
-/
lemma defect_comparison_surjective
    (D : KRData)
    (n : ℕ) :
    Function.Surjective (D.defectComparisonFactor n) := by
  intro y
  rcases ONCompar.relator_comparison_surjective
      initialKochQuotient
      (initialTameRelator D.frobeniusLift)
      (zassenhausOpenSubgroup n)
      D.tameRelatorsKilled y with
    ⟨x, rfl⟩
  exact ⟨D.canonicalKochDefect n x, by
    simpa using congrArg
      (fun ψ : D.ZassenhausRelatorSystem.obj n →*
          InitialKochImage n =>
        ψ x)
      (D.defect_comparison_comp n)⟩

/--
The canonical finite defect quotient comparison factor is injective because
the finite defect quotient kills exactly the comparison kernel.
-/
lemma defect_comparison_injective
    (D : KRData)
    (n : ℕ) :
    Function.Injective (D.defectComparisonFactor n) := by
  apply (MonoidHom.ker_eq_bot_iff
    (D.defectComparisonFactor n)).mp
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_bot]
    rcases D.koch_defect_surjective n y with ⟨x, rfl⟩
    have hcomparison := congrArg
      (fun ψ : D.ZassenhausRelatorSystem.obj n →*
          InitialKochImage n =>
        ψ x)
      (D.defect_comparison_comp n)
    change D.defectComparisonFactor n
        (D.canonicalKochDefect n x) =
      D.relatorImageComparison n x at hcomparison
    have hxcomparison :
        x ∈ (D.relatorImageComparison n).ker := by
      change D.relatorImageComparison n x = 1
      rw [← hcomparison]
      exact MonoidHom.mem_ker.mp hy
    have hxdefect :
        x ∈ (D.canonicalKochDefect n).ker := by
      rw [D.koch_defect_comparison]
      exact hxcomparison
    exact MonoidHom.mem_ker.mp hxdefect
  · exact bot_le

/--
The canonical finite defect quotient is canonically the actual finite quotient
obtained by killing the image of the actual Koch kernel in the underlying
Zassenhaus layer.
-/
def canonicalDefectImage
    (D : KRData)
    (n : ℕ) :
    D.CanonicalKochDefect n ≃*
      InitialKochImage n :=
  MulEquiv.ofBijective
    (D.defectComparisonFactor n)
    ⟨D.defect_comparison_injective n,
      D.defect_comparison_surjective n⟩

/--
The canonical finite defect quotient equivalence is induced by the canonical
finite defect quotient comparison factor.
-/
lemma defect_monoid_hom
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectImage
        n).toMonoidHom =
      D.defectComparisonFactor n := by
  rfl

/--
The canonical equivalence from a finite defect quotient to the actual finite
kernel-image quotient carries the finite defect quotient map to the older
relator-vs-kernel image comparison.
-/
lemma kochDefectComp
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectImage
        n).toMonoidHom.comp
        (D.canonicalKochDefect n) =
      D.relatorImageComparison n := by
  rw [D.defect_monoid_hom]
  exact D.defect_comparison_comp n

/--
After the canonical finite quotient identification, the unconditional finite
defect quotient factor from the actual Galois group is the ordinary actual
finite kernel-image quotient factor.
-/
lemma defect_comp_factor
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectImage
        n).toMonoidHom.comp
        (D.canonicalDefectFactor n) =
      initialKochFactor n := by
  apply MonoidHom.ext
  intro y
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  have hdefect :
      D.canonicalDefectFactor n (initialKochQuotient x) =
        D.canonicalKochDefect n
          ((D.ZassenhausRelatorQuotient n).map x) := by
    exact DFunLike.congr_fun
      (D.canonical_defect_comp n)
      x
  have hfactor := congrArg
    (fun ψ : initialKochFree.Carrier →* InitialKochImage n =>
      ψ x)
    (initial_image_comp n)
  change initialKochFactor n (initialKochQuotient x) =
    initialKochImage n x at hfactor
  change D.canonicalDefectImage n
      (D.canonicalDefectFactor n (initialKochQuotient x)) =
    initialKochFactor n (initialKochQuotient x)
  rw [hdefect]
  calc
    D.canonicalDefectImage n
        (D.canonicalKochDefect n
          ((D.ZassenhausRelatorQuotient n).map x)) =
        D.relatorImageComparison n
          ((D.ZassenhausRelatorQuotient n).map x) :=
      DFunLike.congr_fun
        (D.kochDefectComp
          n)
        ((D.ZassenhausRelatorQuotient n).map x)
    _ = initialKochImage n x :=
      DFunLike.congr_fun
        (D.image_comparison_comp
          n)
        x
    _ = initialKochFactor n (initialKochQuotient x) :=
      hfactor.symm

/--
Canonical finite defect quotient factors are compatible with the canonical
finite defect quotient transition maps.
-/
lemma canonical_defect_factor
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.CanonicalDefectSystem.map hnm).comp
        (D.canonicalDefectFactor m) =
      D.canonicalDefectFactor n := by
  exact D.ZassenhausRelatorSystem.defect_transition_factor
    D.inverseLimitDescent
    D.limit_descent_surjective
    D.limit_projection_surjective
    hnm

/--
The canonical finite defect quotient equivalences identify the canonical
finite defect quotient tower with the actual finite kernel-image quotient
tower.
-/
lemma kochCommutesTransition
    (D : KRData)
    {n m : ℕ}
    (hnm : n ≤ m) :
    (D.canonicalDefectImage
        n).toMonoidHom.comp
        (D.CanonicalDefectSystem.map hnm) =
      (InitialKochSystem.map hnm).comp
        (D.canonicalDefectImage
          m).toMonoidHom := by
  apply MonoidHom.ext
  intro y
  rcases D.canonical_defect_surjective m y with ⟨g, rfl⟩
  have hcanonical := DFunLike.congr_fun
    (D.canonical_defect_factor hnm)
    g
  have hactual := DFunLike.congr_fun
    (initial_comp_factor hnm)
    g
  have hen := DFunLike.congr_fun
    (D.defect_comp_factor
      n)
    g
  have hem := DFunLike.congr_fun
    (D.defect_comp_factor
      m)
    g
  change D.CanonicalDefectSystem.map hnm
      (D.canonicalDefectFactor m g) =
    D.canonicalDefectFactor n g at hcanonical
  change InitialKochSystem.map hnm
      (initialKochFactor m g) =
    initialKochFactor n g at hactual
  change D.canonicalDefectImage n
      (D.canonicalDefectFactor n g) =
    initialKochFactor n g at hen
  change D.canonicalDefectImage m
      (D.canonicalDefectFactor m g) =
    initialKochFactor m g at hem
  change D.canonicalDefectImage n
      (D.CanonicalDefectSystem.map hnm
        (D.canonicalDefectFactor m g)) =
    InitialKochSystem.map hnm
      (D.canonicalDefectImage m
        (D.canonicalDefectFactor m g))
  rw [hcanonical, hen, hem, hactual]

/--
The canonical target equivalence carries the unconditional finite defect
shadow map to the actual finite kernel-image shadow map.
-/
lemma defect_shadow_transport
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectImage
        n).toMonoidHom.comp
        (D.kochDefectShadow n).map =
      (initialImageShadow n).map := by
  change (D.canonicalDefectImage
        n).toMonoidHom.comp
        (D.canonicalDefectFactor n) =
      initialKochFactor n
  exact D.defect_comp_factor
    n

/--
Canonical finite defect shadows and actual finite kernel-image shadows have
the same kernel in the actual initial Galois group.
-/
lemma defect_shadow_image
    (D : KRData)
    (n : ℕ) :
    (D.kochDefectShadow n).map.ker =
      (initialImageShadow n).map.ker := by
  rw [← D.defect_shadow_transport n]
  exact (monoid_ker_comp
    (D.canonicalDefectImage n)
    (D.kochDefectShadow n).map).symm

/--
At one canonical layer, vanishing of the inverse-limit finite defect is
equivalent to injectivity of the older relator-vs-kernel image comparison.
-/
lemma koch_comparison_injective
    (D : KRData)
    (n : ℕ) :
    D.CanonicalDefectSubgroup n = ⊥ ↔
      Function.Injective (D.relatorImageComparison n) := by
  rw [D.defect_image_comparison]
  exact MonoidHom.ker_eq_bot_iff
    (D.relatorImageComparison n)

/--
The desired finite quotient Koch theorem is exactly vanishing of the finite
defect kernels of all canonical relator-vs-kernel image comparisons.
-/
lemma forall_comparison_bot
    (D : KRData) :
    D.KochFactorizationTheorem ↔
      ∀ n : ℕ, (D.relatorImageComparison n).ker = ⊥ := by
  rw [D.forall_defect_bot]
  exact forall_congr' fun n => by
    rw [D.defect_image_comparison]
    rfl

/--
Failure of the desired theorem is detected by one canonical finite comparison
with a nontrivial kernel, equivalently by one nontrivial finite defect image.
-/
lemma not_comparison_bot
    (D : KRData) :
    ¬ D.KochFactorizationTheorem ↔
      ∃ n : ℕ, (D.relatorImageComparison n).ker ≠ ⊥ := by
  rw [D.not_defect_bot]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by
      rw [←
        D.defect_image_comparison]
      exact hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by
      rw [D.defect_image_comparison]
      exact hn⟩

/--
The first finite defect depth is also the first canonical finite comparison
whose kernel is nontrivial.
-/
lemma bot_defect_depth
    (D : KRData)
    (hnot : ¬ D.KochFactorizationTheorem) :
    (D.relatorImageComparison
      (D.canonicalDefectDepth hnot)).ker ≠ ⊥ := by
  rw [← D.defect_image_comparison]
  exact D.ne_bot_depth hnot

/--
Before the first finite defect depth, every canonical finite comparison still
has trivial kernel.
-/
lemma comparison_defect_depth
    (D : KRData)
    (hnot : ¬ D.KochFactorizationTheorem)
    {m : ℕ}
    (hm : m < D.canonicalDefectDepth hnot) :
    (D.relatorImageComparison m).ker = ⊥ := by
  rw [← D.defect_image_comparison]
  exact D.defect_bot_depth hnot hm

end KRData

end TBluepr
end Submission
