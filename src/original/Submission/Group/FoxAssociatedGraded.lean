import Submission.Group.PresentedFox
import Submission.Group.Zassenhaus

noncomputable section

namespace Submission

/-- The mod-`p` augmentation ideal of the free group algebra. -/
abbrev freeAugmentationIdeal (p d : ℕ) :
    Ideal (MonoidAlgebra (ZMod p) (FreeGroup (Fin d))) :=
  GShafar.augmentationIdeal (ZMod p) (FreeGroup (Fin d))

/-- A package for the usual Fox derivatives on a free group over `ZMod p`.

This is not meant to be the final API; it just isolates the Fox-calculus facts
needed later. -/
structure FreeFoxCalculus (p d : ℕ) [Fact p.Prime] where
  deriv :
    FreeGroup (Fin d) → Fin d →
      MonoidAlgebra (ZMod p) (FreeGroup (Fin d))
  fundamental_formula :
    ∀ g : FreeGroup (Fin d),
      augmentationDifference (ZMod p) (FreeGroup (Fin d)) g =
        ∑ j : Fin d,
          deriv g j *
            augmentationDifference (ZMod p) (FreeGroup (Fin d))
              (FreeGroup.of j)
  deriv_zassenhaus :
    ∀ {g : FreeGroup (Fin d)} {n : ℕ},
      g ∈ zassenhausFiltration p (FreeGroup (Fin d)) n →
        ∀ j : Fin d,
          deriv g j ∈ (freeAugmentationIdeal p d) ^ (n - 1)

lemma fox_deriv_depth
    {p d r : ℕ} [Fact p.Prime]
    (D : FreeFoxCalculus p d)
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (i : Fin r) (j : Fin d) :
    D.deriv (rels i) j ∈ (freeAugmentationIdeal p d) ^ (depth i - 1) := by
  exact D.deriv_zassenhaus (hdepth i) j

namespace TBluepr

/-- Sometimes one wants exact Zassenhaus degrees, not just lower bounds. -/
def PresentedDepthsExact
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ) : Prop :=
  (∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i)) ∧
  (∀ i, rels i ∉ zassenhausFiltration p (FreeGroup (Fin d)) (depth i + 1))

lemma presented_augmentation_submodule
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ)
    (a : presentedGroupAlgebra (p := p) rels) :
    a ∈ presentedAugmentationSubmodule (p := p) rels n ↔
      a ∈ (presentedAugmentationIdeal (p := p) rels) ^ n := by
  rfl

lemma presented_submodule_zero
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) :
    presentedAugmentationSubmodule (p := p) rels 0 = ⊤ := by
  simp [presentedAugmentationSubmodule]

lemma presented_submodule_antitone
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    {m n : ℕ} (hmn : m ≤ n) :
    presentedAugmentationSubmodule (p := p) rels n ≤
      presentedAugmentationSubmodule (p := p) rels m := by
  intro a ha
  exact Ideal.pow_le_pow_right hmn ha

lemma presented_submodule_succ
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ) :
    presentedAugmentationSubmodule (p := p) rels (n + 1) ≤
      presentedAugmentationSubmodule (p := p) rels n := by
  exact presented_submodule_antitone rels (Nat.le_add_right n 1)

lemma presented_submodule_mul
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    {m n : ℕ}
    {a b : presentedGroupAlgebra (p := p) rels}
    (ha : a ∈ presentedAugmentationSubmodule (p := p) rels m)
    (hb : b ∈ presentedAugmentationSubmodule (p := p) rels n) :
    a * b ∈ presentedAugmentationSubmodule (p := p) rels (m + n) := by
  have hmul :
      a * b ∈
        (presentedAugmentationIdeal (p := p) rels) ^ m *
          (presentedAugmentationIdeal (p := p) rels) ^ n :=
    Ideal.mul_mem_mul ha hb
  simpa only [← Ideal.IsTwoSided.pow_add] using hmul

lemma presented_difference_aug
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (j : Fin d) :
    presentedGeneratorDifference (p := p) rels j ∈
      presentedAugmentationSubmodule (p := p) rels 1 := by
  simpa [presentedAugmentationSubmodule, Submodule.pow_one] using
    presented_difference_ideal (p := p) rels j

/-- The boundary map raises augmentation degree by one. -/
lemma presented_boundary_aug
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (n : ℕ)
    (y : Fin d → presentedGroupAlgebra (p := p) rels)
    (hy : ∀ j, y j ∈ presentedAugmentationSubmodule (p := p) rels n) :
    (presentedGeneratorBoundary (p := p) rels) y ∈
      presentedAugmentationSubmodule (p := p) rels (n + 1) := by
  classical
  change
    ∑ j, y j * presentedGeneratorDifference (p := p) rels j ∈
      presentedAugmentationSubmodule (p := p) rels (n + 1)
  apply Submodule.sum_mem
  intro j _hj
  exact presented_submodule_mul rels
    (hy j) (presented_difference_aug rels j)

/-- Strictness of the boundary map with respect to the augmentation filtration. -/
lemma boundary_strict_aug
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (n : ℕ)
    {a : presentedGroupAlgebra (p := p) rels}
    (ha : a ∈ presentedAugmentationSubmodule (p := p) rels (n + 1)) :
    ∃ y : Fin d → presentedGroupAlgebra (p := p) rels,
      (∀ j, y j ∈ presentedAugmentationSubmodule (p := p) rels n) ∧
      (presentedGeneratorBoundary (p := p) rels) y = a := by
  let a' : presentedAugmentationSubmodule (p := p) rels (n + 1) := ⟨a, ha⟩
  rcases presented_generated_exact
      (p := p) rels (n + 1) (by omega) a' with
    ⟨y, hy⟩
  refine ⟨fun j => (y j : presentedGroupAlgebra (p := p) rels), ?_, ?_⟩
  · intro j
    exact (y j).2
  · simpa [a', presentedGeneratorBoundary] using hy.symm

lemma presented_augmentation_layer
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ)
    (x : presentedAugmentationSubmodule (p := p) rels n) :
    x ∈ presentedAugmentationKernel (p := p) rels n ↔
      ((x : presentedGroupAlgebra (p := p) rels) ∈
        presentedAugmentationSubmodule (p := p) rels (n + 1)) := by
  rfl

lemma presented_filtration_succ
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ) :
    presentedModuleFiltration (p := p) rels (n + 1) ≤
      presentedModuleFiltration (p := p) rels n := by
  exact presented_filtration_antitone rels (Nat.le_add_right n 1)

lemma presented_relation_module
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ)
    (x : presentedModuleFiltration (p := p) rels n) :
    x ∈ presentedModuleKernel (p := p) rels n ↔
      ((x : presentedRelationModule (p := p) rels) ∈
        presentedModuleFiltration (p := p) rels (n + 1)) := by
  rfl

/-- Initial-kernel lifting: a vector whose boundary is one order too deep is
congruent, modulo the next filtration step, to an actual relation. -/
lemma presented_boundary_lift
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (m : ℕ)
    (y : Fin d → presentedGroupAlgebra (p := p) rels)
    (hy : ∀ j, y j ∈ presentedAugmentationSubmodule (p := p) rels m)
    (hboundary :
      (presentedGeneratorBoundary (p := p) rels) y ∈
        presentedAugmentationSubmodule (p := p) rels (m + 2)) :
    ∃ x : presentedModuleFiltration (p := p) rels m,
      ∀ j,
        ((((x : presentedRelationModule (p := p) rels) :
            Fin d → presentedGroupAlgebra (p := p) rels) j) - y j) ∈
          presentedAugmentationSubmodule (p := p) rels (m + 1) := by
  rcases boundary_strict_aug rels (m + 1)
      (by simpa [Nat.add_assoc] using hboundary) with
    ⟨z, hz, hzboundary⟩
  let x : presentedRelationModule (p := p) rels :=
    ⟨fun j => y j - z j, by
      change
        (presentedGeneratorBoundary (p := p) rels) (y - z) = 0
      rw [map_sub, hzboundary, sub_self]⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · intro j
    dsimp [x]
    exact (presentedAugmentationSubmodule (p := p) rels m).sub_mem
      (hy j)
      (presented_submodule_antitone rels
        (Nat.le_add_right m 1) (hz j))
  · intro j
    dsimp [x]
    simpa using
      (presentedAugmentationSubmodule (p := p) rels (m + 1)).neg_mem (hz j)

/-- Equality in a relation-module layer follows from coordinatewise congruence
modulo the next augmentation power. -/
lemma presented_q_congr
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    {m : ℕ}
    {x y : presentedModuleFiltration (p := p) rels m}
    (hxy :
      ∀ j,
        ((((x : presentedRelationModule (p := p) rels) :
            Fin d → presentedGroupAlgebra (p := p) rels) j) -
          (((y : presentedRelationModule (p := p) rels) :
            Fin d → presentedGroupAlgebra (p := p) rels) j)) ∈
          presentedAugmentationSubmodule (p := p) rels (m + 1)) :
    (Submodule.mkQ
      (presentedModuleKernel (p := p) rels m)) x =
    (Submodule.mkQ
      (presentedModuleKernel (p := p) rels m)) y := by
  apply (Submodule.Quotient.eq
    (presentedModuleKernel (p := p) rels m)).mpr
  rw [presented_relation_module]
  exact hxy

set_option synthInstance.maxHeartbeats 200000 in
-- Instance synthesis unfolds nested quotient modules in the target.
/-- The original `lsum` map expands as the sum of the component maps. -/
lemma presented_high_layer
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (x : pHSrc (p := p) rels depth n) :
    (presentedHighLayer
      (p := p) rels depth hdepth hdepth2 n) x =
      ∑ i : pARelato depth n,
        presentedRelationSingle
          (p := p) rels depth hdepth hdepth2 n i (x i) := by
  simp [presentedHighLayer, LinearMap.lsum_apply]

/-- The data of the Fox-gradient vectors of the relators after passing to the
presented group algebra. -/
structure PFJacobi
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ) where
  coeff : Fin r → Fin d → presentedGroupAlgebra (p := p) rels
  coeff_mem :
    ∀ i j,
      coeff i j ∈
        presentedAugmentationSubmodule (p := p) rels (depth i - 1)
  boundary_zero :
    ∀ i,
      (presentedGeneratorBoundary (p := p) rels) (coeff i) = 0

namespace PFJacobi

variable {p d r : ℕ} [Fact p.Prime]
variable {rels : Fin r → FreeGroup (Fin d)}
variable {depth : Fin r → ℕ}

/-- The Fox-gradient vector of a relator, regarded as an element of the relation
module. -/
noncomputable def relation
    (Φ : PFJacobi (p := p) rels depth)
    (i : Fin r) :
    presentedRelationModule (p := p) rels :=
  ⟨Φ.coeff i, by
    change (presentedGeneratorBoundary (p := p) rels) (Φ.coeff i) = 0
    exact Φ.boundary_zero i⟩

@[simp] lemma relation_apply
    (Φ : PFJacobi (p := p) rels depth)
    (i : Fin r) (j : Fin d) :
    ((Φ.relation i : Fin d → presentedGroupAlgebra (p := p) rels) j) =
      Φ.coeff i j := by
  rfl

lemma relation_mem_filtration
    (Φ : PFJacobi (p := p) rels depth)
    (i : Fin r) :
    Φ.relation i ∈
      presentedModuleFiltration (p := p) rels (depth i - 1) := by
  rw [presented_relation_filtration]
  exact Φ.coeff_mem i

/-- Left-multiply a Fox-gradient relation vector by an algebra element. -/
noncomputable def leftMulRelation
    (Φ : PFJacobi (p := p) rels depth)
    (i : Fin r)
    (a : presentedGroupAlgebra (p := p) rels) :
    presentedRelationModule (p := p) rels :=
  ⟨fun j => a * Φ.coeff i j, by
    change
      (presentedGeneratorBoundary (p := p) rels)
        (fun j => a * Φ.coeff i j) = 0
    classical
    calc
      ∑ j, (a * Φ.coeff i j) *
            presentedGeneratorDifference (p := p) rels j =
          a * ∑ j, Φ.coeff i j *
            presentedGeneratorDifference (p := p) rels j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [mul_assoc]
      _ = a *
          (presentedGeneratorBoundary (p := p) rels) (Φ.coeff i) := rfl
      _ = 0 := by rw [Φ.boundary_zero i, mul_zero]⟩

@[simp] lemma left_mul_relation
    (Φ : PFJacobi (p := p) rels depth)
    (i : Fin r)
    (a : presentedGroupAlgebra (p := p) rels)
    (j : Fin d) :
    ((Φ.leftMulRelation i a :
        Fin d → presentedGroupAlgebra (p := p) rels) j) =
      a * Φ.coeff i j := by
  rfl

lemma left_relation_filtration
    (Φ : PFJacobi (p := p) rels depth)
    {n : ℕ}
    (i : Fin r)
    (hi : depth i ≤ n)
    {a : presentedGroupAlgebra (p := p) rels}
    (ha : a ∈ presentedAugmentationSubmodule (p := p) rels (n - depth i)) :
    Φ.leftMulRelation i a ∈
      presentedModuleFiltration (p := p) rels (n - 1) := by
  rw [presented_relation_filtration]
  intro j
  apply presented_submodule_antitone rels
    (m := n - 1) (n := (n - depth i) + (depth i - 1)) (by omega)
  exact presented_submodule_mul rels ha (Φ.coeff_mem i j)

lemma relation_congr_mod
    (Φ : PFJacobi (p := p) rels depth)
    {n : ℕ}
    (i : Fin r)
    (hi : depth i ≤ n)
    {a b : presentedGroupAlgebra (p := p) rels}
    (hab :
      a - b ∈
        presentedAugmentationSubmodule
          (p := p) rels ((n - depth i) + 1)) :
    Φ.leftMulRelation i a - Φ.leftMulRelation i b ∈
      presentedModuleFiltration (p := p) rels n := by
  rw [presented_relation_filtration]
  intro j
  change
    a * Φ.coeff i j - b * Φ.coeff i j ∈
      presentedAugmentationSubmodule (p := p) rels n
  rw [← sub_mul]
  apply presented_submodule_antitone rels
    (m := n) (n := ((n - depth i) + 1) + (depth i - 1)) (by omega)
  exact presented_submodule_mul rels hab (Φ.coeff_mem i j)

/-- The filtered map induced by multiplying the `i`th Fox-gradient vector. -/
noncomputable def leftMulFiltered
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (i : pARelato depth n) :
    presentedAugmentationSubmodule (p := p) rels (n - depth i.1) →ₗ[ZMod p]
      presentedModuleFiltration (p := p) rels (n - 1) where
  toFun a :=
    ⟨Φ.leftMulRelation i.1
        (a : presentedGroupAlgebra (p := p) rels), by
      exact
        PFJacobi.left_relation_filtration
          (Φ := Φ) (n := n) i.1 i.2
          (a := (a : presentedGroupAlgebra (p := p) rels)) a.2⟩
  map_add' := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp [leftMulRelation, add_mul]
  map_smul' := by
    intro c a
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp [leftMulRelation]

lemma filtered_maps_kernel
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (i : pARelato depth n) :
    presentedAugmentationKernel (p := p) rels (n - depth i.1) ≤
      (presentedModuleKernel (p := p) rels (n - 1)).comap
        (Φ.leftMulFiltered n i) := by
  intro a ha
  change
    Φ.leftMulFiltered n i a ∈
      presentedModuleKernel (p := p) rels (n - 1)
  rw [presented_relation_module]
  rw [presented_relation_filtration]
  intro j
  change
    (a : presentedGroupAlgebra (p := p) rels) * Φ.coeff i.1 j ∈
      presentedAugmentationSubmodule (p := p) rels ((n - 1) + 1)
  apply presented_submodule_antitone rels
    (m := (n - 1) + 1) (n := ((n - depth i.1) + 1) + (depth i.1 - 1)) (by omega)
  exact presented_submodule_mul rels
    ((presented_augmentation_layer rels (n - depth i.1) a).mp ha)
    (Φ.coeff_mem i.1 j)

/-- The induced map on associated-graded layers corresponding to one relator. -/
noncomputable def singleLayerMap
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (i : pARelato depth n) :
    pALayer (p := p) rels (n - depth i.1) →ₗ[ZMod p]
      presentedModuleLayer (p := p) rels (n - 1) :=
  Submodule.mapQ
    (presentedAugmentationKernel (p := p) rels (n - depth i.1))
    (presentedModuleKernel (p := p) rels (n - 1))
    (Φ.leftMulFiltered n i)
    (Φ.filtered_maps_kernel n i)

set_option synthInstance.maxHeartbeats 200000 in
-- Instance synthesis unfolds nested quotient modules on both sides.
lemma single_mk_q
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (i : pARelato depth n) :
    (Φ.singleLayerMap n i).comp
        (Submodule.mkQ
          (presentedAugmentationKernel
            (p := p) rels (n - depth i.1))) =
      (Submodule.mkQ
        (presentedModuleKernel
          (p := p) rels (n - 1))).comp
        (Φ.leftMulFiltered n i) := by
  exact Submodule.mapQ_mkQ _ _ _

/-- The sum of the filtered Fox-gradient contributions. -/
noncomputable def sumFilteredRelation
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (c :
      ∀ i : pARelato depth n,
        presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1)) :
    presentedModuleFiltration (p := p) rels (n - 1) :=
  ∑ i : pARelato depth n,
    Φ.leftMulFiltered n i (c i)

lemma sum_filtered_relation
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (c :
      ∀ i : pARelato depth n,
        presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1))
    (j : Fin d) :
    ((((Φ.sumFilteredRelation n c :
          presentedRelationModule (p := p) rels) :
          Fin d → presentedGroupAlgebra (p := p) rels) j)) =
      ∑ i : pARelato depth n,
        ((c i : presentedGroupAlgebra (p := p) rels) *
          Φ.coeff i.1 j) := by
  classical
  simp [sumFilteredRelation, leftMulFiltered, leftMulRelation]

/-- Turn representatives in the source filtration into source layer classes. -/
noncomputable def sourceClassCoefficients
    (_Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (c :
      ∀ i : pARelato depth n,
        presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1)) :
    pHSrc (p := p) rels depth n :=
  fun i =>
    (Submodule.mkQ
      (presentedAugmentationKernel
        (p := p) rels (n - depth i.1))) (c i)

/-- The corrected high-degree relator map built from Fox derivatives. -/
noncomputable def foxHighLayer
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ) :
    pHSrc (p := p) rels depth n →ₗ[ZMod p]
      presentedModuleLayer (p := p) rels (n - 1) :=
  LinearMap.lsum (ZMod p)
    (fun i : pARelato depth n =>
      pALayer (p := p) rels (n - depth i.1))
    (ZMod p)
    (fun i => Φ.singleLayerMap n i)

set_option synthInstance.maxHeartbeats 200000 in
-- Instance synthesis unfolds nested quotient modules in the target.
lemma fox_high_layer
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (x : pHSrc (p := p) rels depth n) :
    Φ.foxHighLayer n x =
      ∑ i : pARelato depth n,
        Φ.singleLayerMap n i (x i) := by
  simp [foxHighLayer, LinearMap.lsum_apply]

set_option synthInstance.maxHeartbeats 200000 in
-- Instance synthesis unfolds nested quotient modules in the target.
lemma fox_high_coefficients
    (Φ : PFJacobi (p := p) rels depth)
    (n : ℕ)
    (c :
      ∀ i : pARelato depth n,
        presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1)) :
    Φ.foxHighLayer n
        (Φ.sourceClassCoefficients n c) =
      (Submodule.mkQ
        (presentedModuleKernel
          (p := p) rels (n - 1)))
        (Φ.sumFilteredRelation n c) := by
  classical
  rw [Φ.fox_high_layer]
  change
    (∑ i : pARelato depth n,
      (Submodule.mkQ
        (presentedModuleKernel (p := p) rels (n - 1)))
        (Φ.leftMulFiltered n i (c i))) =
      (Submodule.mkQ
        (presentedModuleKernel (p := p) rels (n - 1)))
        (∑ i : pARelato depth n, Φ.leftMulFiltered n i (c i))
  exact (map_sum
    (Submodule.mkQ (presentedModuleKernel (p := p) rels (n - 1)))
    (fun i : pARelato depth n => Φ.leftMulFiltered n i (c i))
    Finset.univ).symm

end PFJacobi

/-- The associated-graded generation statement for the corrected Fox map. -/
def AssociatedGradedGeneration
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (Φ : PFJacobi (p := p) rels depth) : Prop :=
  ∀ n (_hn : 2 ≤ n),
    Function.Surjective
      (Φ.foxHighLayer n)

/-- Jennings-Fox exactness, stated directly in representatives.

A vector `y` of degree `n - 1` whose boundary is in degree `n + 1`
is, modulo degree `n`, generated by the initial Fox-gradient vectors of the
active relators. -/
def PresentedFoxExactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (Φ : PFJacobi (p := p) rels depth) : Prop :=
  ∀ n (_hn : 2 ≤ n)
    (y : Fin d → presentedGroupAlgebra (p := p) rels),
      (∀ j, y j ∈
        presentedAugmentationSubmodule (p := p) rels (n - 1)) →
      (presentedGeneratorBoundary (p := p) rels) y ∈
        presentedAugmentationSubmodule (p := p) rels (n + 1) →
      ∃ c :
        ∀ _i : pARelato depth n,
          presentedGroupAlgebra (p := p) rels,
        (∀ i, c i ∈
          presentedAugmentationSubmodule
            (p := p) rels (n - depth i.1)) ∧
        ∀ j,
          (y j -
            ∑ i : pARelato depth n,
              c i * Φ.coeff i.1 j) ∈
            presentedAugmentationSubmodule (p := p) rels n

lemma representative_generated_exactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (Φ : PFJacobi (p := p) rels depth)
    (hJF : PresentedFoxExactness (p := p) rels depth Φ)
    {n : ℕ} (hn : 2 ≤ n)
    (x : presentedModuleFiltration (p := p) rels (n - 1)) :
    ∃ c :
      ∀ i : pARelato depth n,
        presentedAugmentationSubmodule
          (p := p) rels (n - depth i.1),
      ∀ j,
        ((((x : presentedRelationModule (p := p) rels) :
            Fin d → presentedGroupAlgebra (p := p) rels) j) -
          ∑ i : pARelato depth n,
            ((c i : presentedGroupAlgebra (p := p) rels) *
              Φ.coeff i.1 j)) ∈
          presentedAugmentationSubmodule (p := p) rels n := by
  let y : Fin d → presentedGroupAlgebra (p := p) rels :=
    (x : presentedRelationModule (p := p) rels)
  have hy :
      ∀ j, y j ∈
        presentedAugmentationSubmodule (p := p) rels (n - 1) :=
    x.2
  have hboundary :
      (presentedGeneratorBoundary (p := p) rels) y ∈
        presentedAugmentationSubmodule (p := p) rels (n + 1) := by
    have hzero :
        (presentedGeneratorBoundary (p := p) rels) y = 0 :=
      LinearMap.mem_ker.mp ((x : presentedRelationModule (p := p) rels).2)
    rw [hzero]
    exact (presentedAugmentationSubmodule (p := p) rels (n + 1)).zero_mem
  rcases hJF n hn y hy hboundary with ⟨c, hc, hcoord⟩
  exact ⟨fun i => ⟨c i, hc i⟩, hcoord⟩

theorem fox_generation_exactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (Φ : PFJacobi (p := p) rels depth)
    (hJF : PresentedFoxExactness (p := p) rels depth Φ) :
    AssociatedGradedGeneration
      (p := p) rels depth Φ := by
  intro n hn z
  have hn1 : 1 ≤ n := by omega
  refine Submodule.Quotient.induction_on
    (p := presentedModuleKernel (p := p) rels (n - 1)) z ?_
  intro x
  rcases representative_generated_exactness
      rels depth Φ hJF hn x with ⟨c, hc⟩
  refine ⟨Φ.sourceClassCoefficients n c, ?_⟩
  rw [Φ.fox_high_coefficients]
  exact (presented_q_congr rels (fun j => by
    simpa only [Φ.sum_filtered_relation, Nat.sub_add_cancel hn1] using hc j)).symm

/-- Compatibility between the genuine Fox layer maps and the map currently used
in the theorem statement.  With the code as written, the RHS is the zero map,
so this compatibility is the place where the placeholder definition must be
replaced by the true Fox map. -/
def PresentedAgreesCode
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (Φ : PFJacobi (p := p) rels depth) : Prop :=
  ∀ n (i : pARelato depth n),
    Φ.singleLayerMap n i =
      presentedRelationSingle
        (p := p) rels depth hdepth hdepth2 n i

lemma fox_high_code
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (Φ : PFJacobi (p := p) rels depth)
    (hcompat :
      PresentedAgreesCode
        (p := p) rels depth hdepth hdepth2 Φ)
    (n : ℕ) :
    Φ.foxHighLayer n =
      presentedHighLayer
        (p := p) rels depth hdepth hdepth2 n := by
  apply LinearMap.ext
  intro x
  rw [Φ.fox_high_layer]
  rw [presented_high_layer
    (p := p) rels depth hdepth hdepth2 n x]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hcompat n i]

/-- Final bridge theorem: Jennings-Fox exactness for the genuine Fox maps implies
the theorem statement, provided the theorem statement's map is definitionally or
propositionally the genuine Fox map. -/
theorem graded_generation_exactness
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (Φ : PFJacobi (p := p) rels depth)
    (hcompat :
      PresentedAgreesCode
        (p := p) rels depth hdepth hdepth2 Φ)
    (hJF : PresentedFoxExactness (p := p) rels depth Φ) :
    PresentedGradedGeneration
      (p := p) rels depth hdepth hdepth2 := by
  intro n hn
  rw [← fox_high_code
    rels depth hdepth hdepth2 Φ hcompat n]
  exact fox_generation_exactness rels depth Φ hJF n hn

end TBluepr

end Submission
