import Submission.Group.FinitePGS


open scoped BigOperators AlgebraMonoidAlgebra

noncomputable section

universe u

namespace Submission
namespace GShafar

/-- Relators for a presentation on `d` generators and `r` relations. -/
def RelatorFamily (d r : ℕ) : Type :=
  Fin r → FreeGroup (Fin d)

/-- The group presented by a finite relator family. -/
def pGroup {d r : ℕ} (rels : RelatorFamily d r) : Type :=
  PresentedGroup (Set.range rels)

/-- The group structure inherited from `PresentedGroup`. -/
instance pGroup.instGroup {d r : ℕ} (rels : RelatorFamily d r) :
    Group (pGroup rels) := by
  unfold pGroup
  infer_instance

/-- A relator family presents the group `G`. -/
def PresentationRealizes {G : Type*} [Group G] {d r : ℕ}
    (rels : RelatorFamily d r) : Prop :=
  Nonempty (pGroup rels ≃* G)

def presentedGroupAlgebra {d r : ℕ} (p : ℕ) (rels : RelatorFamily d r) : Type :=
  MonoidAlgebra (ZMod p) (pGroup rels)

/--
The group-algebra map induced by the quotient from the free group to the
presented group.
-/
def presentedFreeAlgebra {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) :
    MonoidAlgebra (ZMod p) (FreeGroup (Fin d)) →+*
      MonoidAlgebra (ZMod p) (pGroup rels) :=
  MonoidAlgebra.mapDomainRingHom (ZMod p) (PresentedGroup.mk (Set.range rels))

/-- The augmentation difference attached to a presentation generator. -/
def presentedGeneratorDifference {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (j : Fin d) :
    MonoidAlgebra (ZMod p) (pGroup rels) :=
  augmentationDifference (ZMod p) (pGroup rels)
    (PresentedGroup.of (rels := Set.range rels) j)

/-- The free-group Fox derivative of a selected relator. -/
def relatorFoxDerivative {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (i : Fin r) (j : Fin d) :
    MonoidAlgebra (ZMod p) (FreeGroup (Fin d)) :=
  groupFoxDerivative (ZMod p) j (rels i)

/-- The pushed-forward Fox coefficient of a presentation relator. -/
def presentedFoxCoefficient {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (i : Fin r) (j : Fin d) :
    MonoidAlgebra (ZMod p) (pGroup rels) :=
  presentedFreeAlgebra p rels
    (relatorFoxDerivative p rels i j)

/-- The quotient map sends free-group augmentation differences to presented ones. -/
lemma presented_free_difference {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (g : FreeGroup (Fin d)) :
    presentedFreeAlgebra p rels
        (augmentationDifference (ZMod p) (FreeGroup (Fin d)) g) =
      augmentationDifference
        (ZMod p)
        (pGroup rels)
        (PresentedGroup.mk (Set.range rels) g) := by
  unfold presentedFreeAlgebra augmentationDifference
  rw [map_sub]
  change
    MonoidAlgebra.mapDomain
        ((PresentedGroup.mk (Set.range rels)) :
          FreeGroup (Fin d) →* pGroup rels)
        (MonoidAlgebra.single g (1 : ZMod p)) -
      MonoidAlgebra.mapDomain
        ((PresentedGroup.mk (Set.range rels)) :
          FreeGroup (Fin d) →* pGroup rels)
        (1 : MonoidAlgebra (ZMod p) (FreeGroup (Fin d))) =
      (MonoidAlgebra.single
        (((PresentedGroup.mk (Set.range rels)) :
          FreeGroup (Fin d) →* pGroup rels) g)
        (1 : ZMod p) : MonoidAlgebra (ZMod p) (pGroup rels)) -
          (1 : MonoidAlgebra (ZMod p) (pGroup rels))
  rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapDomain_one]
  rfl

lemma presented_difference_zero {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (i : Fin r) :
    presentedFreeAlgebra p rels
        (augmentationDifference (ZMod p) (FreeGroup (Fin d)) (rels i)) =
      0 := by
  rw [presented_free_difference]
  have hrel :
      PresentedGroup.mk (Set.range rels) (rels i) = 1 :=
    PresentedGroup.one_of_mem (rels := Set.range rels) ⟨i, rfl⟩
  rw [hrel]
  unfold augmentationDifference
  rw [MonoidAlgebra.one_def]
  exact sub_self (MonoidAlgebra.single (1 : pGroup rels) (1 : ZMod p))

/--
The Fox identity for a defining relator after passing to the presented group
algebra.

This is the numerator-level syzygy behind the relator-to-generator map:
the pushed-forward Fox derivatives of a relator multiply the presentation
generator differences to zero.
-/
theorem presented_relator_syzygy {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (i : Fin r) :
    ∑ j,
        presentedFoxCoefficient p rels i j *
          presentedGeneratorDifference p rels j =
      0 := by
  classical
  let R := ZMod p
  let F := FreeGroup (Fin d)
  let A := MonoidAlgebra R (pGroup rels)
  let q : MonoidAlgebra R F →+* A := presentedFreeAlgebra p rels
  have hmap_sum :
      q (∑ j,
          groupFoxDerivative R j (rels i) *
            augmentationDifference R F (FreeGroup.of j)) =
        ∑ j,
          q (groupFoxDerivative R j (rels i)) *
            presentedGeneratorDifference p rels j := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_mul]
    rw [presented_free_difference]
    simp [presentedGeneratorDifference, PresentedGroup.of, R, F, q]
  have hfox :
      augmentationDifference R F (rels i) =
        ∑ j,
          groupFoxDerivative R j (rels i) *
            augmentationDifference R F (FreeGroup.of j) :=
    by
      simpa [groupFoxDerivative, FreeGroup.mk_toWord] using
        fox_derivative_fundamental R (rels i).toWord
  calc
    ∑ j,
        presentedFoxCoefficient p rels i j *
          presentedGeneratorDifference p rels j
        = q (∑ j,
            groupFoxDerivative R j (rels i) *
              augmentationDifference R F (FreeGroup.of j)) := by
          simpa [presentedFoxCoefficient, relatorFoxDerivative, R, F, A, q] using
            hmap_sum.symm
    _ = q (augmentationDifference R F (rels i)) := by
          rw [← hfox]
    _ = 0 := by
          simpa [R, F, A, q] using
            presented_difference_zero p rels i

/-- The augmentation ideal of a presented group algebra over `𝔽_p`. -/
def presentedAugmentationIdeal {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) :
    Ideal (MonoidAlgebra (ZMod p) (pGroup rels)) :=
  augmentationIdeal (ZMod p) (pGroup rels)

lemma presented_generator_difference {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (j : Fin d) :
    presentedGeneratorDifference p rels j ∈
      (presentedAugmentationIdeal p rels) ^ 1 := by
  change presentedGeneratorDifference p rels j ∈
    (1 : Ideal (MonoidAlgebra (ZMod p) (pGroup rels))) *
      presentedAugmentationIdeal p rels
  simpa using
    Ideal.mul_mem_mul
      (show (1 : MonoidAlgebra (ZMod p) (pGroup rels)) ∈
          (1 : Ideal (MonoidAlgebra (ZMod p) (pGroup rels))) by
        simp)
      (show presentedGeneratorDifference p rels j ∈
          presentedAugmentationIdeal p rels by
        exact augmentation_difference_ideal
          (ZMod p)
          (pGroup rels)
          (PresentedGroup.of (rels := Set.range rels) j))

/-- The `n`th augmentation-power submodule, viewed over `𝔽_p`. -/
def presentedAugmentationSubmodule {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (n : ℕ) :
    Submodule (ZMod p) (MonoidAlgebra (ZMod p) (pGroup rels)) :=
  ((presentedAugmentationIdeal p rels) ^ n).restrictScalars (ZMod p)

/--
The denominator `I^(n+1)` inside the numerator `I^n` for the `n`th graded
augmentation layer.
-/
def presentedAugmentationKernel {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (n : ℕ) :
    Submodule (ZMod p)
      (presentedAugmentationSubmodule p rels n) :=
  (presentedAugmentationSubmodule p rels (n + 1)).comap
    (Submodule.subtype (presentedAugmentationSubmodule p rels n))

/-- The `n`th associated-graded augmentation layer `I^n / I^(n+1)`. -/
def pALayer {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (n : ℕ) : Type :=
  (↥(presentedAugmentationSubmodule p rels n)) ⧸
    presentedAugmentationKernel p rels n

/-- The module structure on a presented augmentation layer. -/
instance pALayer.addCommGroup {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (n : ℕ) :
    AddCommGroup (pALayer p rels n) := by
  unfold pALayer
  infer_instance

/-- The module structure on a presented augmentation layer. -/
instance pALayer.instModule {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (n : ℕ) :
    Module (ZMod p) (pALayer p rels n) := by
  unfold pALayer
  exact Submodule.Quotient.module
    (presentedAugmentationKernel p rels n)

/--
For a finite presented group, every augmentation layer over `𝔽_p` is finite
dimensional.  This is the finiteness input needed by the Hilbert-series
recurrence in the finite `p`-group case.
-/
theorem presented_dimensional_group {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (n : ℕ)
    [Finite (pGroup rels)] :
    FiniteDimensional (ZMod p) (pALayer p rels n) := by
  classical
  haveI : Fintype (pGroup rels) := Fintype.ofFinite _
  haveI :
      FiniteDimensional (ZMod p)
        (MonoidAlgebra (ZMod p) (pGroup rels)) := by
    infer_instance
  haveI :
      FiniteDimensional (ZMod p)
        (presentedAugmentationSubmodule p rels n) := by
    infer_instance
  change
    FiniteDimensional (ZMod p)
      ((presentedAugmentationSubmodule p rels n) ⧸
        presentedAugmentationKernel p rels n)
  infer_instance

def presentedAugmentationFinrank {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (n : ℕ) : ℕ :=
  Module.finrank (ZMod p) (pALayer p rels n)

/-- The concrete Hilbert coefficient sequence attached to a presentation. -/
def presentedHilbertSequence {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) : ℕ → ℕ :=
  fun n => presentedAugmentationFinrank p rels n

/-- Generator indices contributing to the degree-`n` recurrence. -/
def aGIndex (d n : ℕ) : Type :=
  {_j : Fin d // 1 ≤ n}

instance aGIndex.instFintype (d n : ℕ) :
    Fintype (aGIndex d n) := by
  classical
  unfold aGIndex
  infer_instance

/-- Relators whose declared depth contributes to the degree-`n` recurrence. -/
def aRIndex {r : ℕ} (depth : Fin r → ℕ) (n : ℕ) : Type :=
  {i : Fin r // depth i ≤ n}

instance aRIndex.instFintype {r : ℕ} (depth : Fin r → ℕ) (n : ℕ) :
    Fintype (aRIndex depth n) := by
  classical
  unfold aRIndex
  infer_instance

/--
The relator-side correction source in degree `n`: one shifted augmentation
layer for each relator whose declared depth is at most `n`.
-/
def presentedHilbertSource {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (depth : Fin r → ℕ) (n : ℕ) : Type :=
  (i : aRIndex depth n) →
    pALayer p rels (n - depth i.1)

/-- The `𝔽_p`-dimension of the generator-side source in degree `n`. -/
def presentedHilbertFinrank {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r) (n : ℕ) : ℕ :=
  Module.finrank (ZMod p)
    (aGIndex d n →
      pALayer p rels (n - 1))

/-- The `𝔽_p`-dimension of the relator-side correction source in degree `n`. -/
def presentedHilbertRelator {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r)
    (depth : Fin r → ℕ) (n : ℕ) : ℕ :=
  Module.finrank (ZMod p)
    ((i : aRIndex depth n) →
      pALayer p rels (n - depth i.1))

/--
The dimension inequality expected from the associated-graded Fox complex in
degree `n`, before simplifying the source dimensions into the scalar
coefficient recurrence.
-/
def PresentationHilbertInequality {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r)
    (depth : Fin r → ℕ) (n : ℕ) : Prop :=
  presentedHilbertFinrank p rels n ≤
    presentedAugmentationFinrank p rels n +
      presentedHilbertRelator p rels depth n

/--
A presentation has the concrete associated-graded dimension inequalities in
every degree.
-/
def PHBounds {d r : ℕ}
    (p : ℕ) [Fact p.Prime] (rels : RelatorFamily d r)
    (depth : Fin r → ℕ) : Prop :=
  ∀ n, PresentationHilbertInequality p rels depth n

/-- `G` admits a generating family of size `n`. -/
def GeneratorCountWitness (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∃ φ : FreeGroup (Fin n) →* G, Function.Surjective φ

/-- The possible cardinalities of finite generating families for `G`. -/
def generatorCounts (G : Type*) [Group G] : Set ℕ :=
  {n | GeneratorCountWitness G n}

/-- The minimal number of generators of `G`, as a natural-number infimum. -/
def generatorRank (G : Type*) [Group G] : ℕ :=
  sInf (generatorCounts G)

/-- `G` has a presentation with `d` generators and `r` relators. -/
def RelationCountWitness (G : Type*) [Group G] (d r : ℕ) : Prop :=
  ∃ rels : RelatorFamily d r, PresentationRealizes (G := G) rels

/-- The possible relation counts for presentations on a fixed number of generators. -/
def relationCountsGenerators (G : Type*) [Group G] (d : ℕ) : Set ℕ :=
  {r | RelationCountWitness G d r}

/--
The minimal number of relators among presentations on a minimal number of
generators.
-/
def relationRank (G : Type*) [Group G] : ℕ :=
  sInf (relationCountsGenerators G (generatorRank G))

/-- A finite presentation is minimal in both generators and relators. -/
def IsMinimalPresentation {G : Type*} [Group G] {d r : ℕ}
    (rels : RelatorFamily d r) : Prop :=
  PresentationRealizes (G := G) rels ∧
    d = generatorRank G ∧
    r = relationRank G

/-- A free-group relator has Zassenhaus depth at least `n`. -/
def RelatorDepthLeast {d : ℕ} (p : ℕ) (rel : FreeGroup (Fin d)) (n : ℕ) : Prop :=
  rel ∈ zassenhausFiltration p (FreeGroup (Fin d)) n

/-- A free-group relator has exact Zassenhaus depth `n`. -/
def RelatorDepthExact {d : ℕ} (p : ℕ) (rel : FreeGroup (Fin d)) (n : ℕ) : Prop :=
  RelatorDepthLeast p rel n ∧ ¬ RelatorDepthLeast p rel (n + 1)

/-- A presentation has the declared lower bounds on all relator depths. -/
def PresentationDepthsLeast {d r : ℕ} (p : ℕ)
    (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  ∀ i, RelatorDepthLeast p (rels i) (depth i)

/-- A presentation has the declared exact relator depths. -/
def PresentationDepthsExact {d r : ℕ} (p : ℕ)
    (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  ∀ i, RelatorDepthExact p (rels i) (depth i)

def PresentationFoxBounds {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  ∀ i j,
    presentedFoxCoefficient p rels i j ∈
      (presentedAugmentationIdeal p rels) ^ (depth i - 1)

/--
The depth data needed to build the associated-graded Fox maps for a
presentation.
-/
def PFFox {d r : ℕ}
    (p : ℕ) (rels : RelatorFamily d r) (depth : Fin r → ℕ) : Prop :=
  PresentationDepthsLeast p rels depth ∧
    (∀ i, 2 ≤ depth i) ∧
    PresentationFoxBounds p rels depth

/-- Filtered Fox data includes the Fox-coefficient depth estimates. -/
theorem PFFox.foxDepthBounds {d r : ℕ} {p : ℕ}
    {rels : RelatorFamily d r} {depth : Fin r → ℕ}
    (h : PFFox p rels depth) :
    PresentationFoxBounds p rels depth :=
  h.2.2

end GShafar
end Submission
