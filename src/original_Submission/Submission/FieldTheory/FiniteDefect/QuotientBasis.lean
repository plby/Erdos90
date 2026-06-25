import Submission.FieldTheory.QuotientKoch.FiniteCorrespondence
import Submission.Group.FinitePQuotient.KernelCofinalFamilies


open scoped Pointwise Topology commutatorElement

noncomputable section

namespace Submission
namespace TBluepr

open KPScaffo
open IGScaffo
open IRScaffo
open PCShadow
open PRFact
open PRQuotie
open TFFact

private instance initialThreeFact : Fact (Nat.Prime 3) :=
  ⟨Nat.prime_three⟩

namespace KRData

/--
Package one honest finite kernel-image stage as an actual surjective finite
`3`-group quotient of the actual initial Galois group.
-/
def initialKochShadow
    (n : ℕ) :
    InitialKochQuotient where
  toShadow := initialImageShadow n
  map_surjective := initial_shadow_surjective n

/--
The honest finite kernel-image quotient shadow map is its named quotient
factor from the actual initial Galois group.
-/
@[simp]
lemma initial_koch_shadow
    (n : ℕ) :
    (initialKochShadow n).map =
      initialKochFactor n := rfl

/--
Every actual finite `3`-group quotient of the actual initial Galois group lies
above one honest finite kernel-image quotient shadow.
-/
lemma initial_koch_three
    (D : KRData)
    (S : InitialKochQuotient) :
    ∃ n : ℕ,
      (initialKochShadow n).map.ker ≤
        S.map.ker := by
  let n := D.ShadowTargetDepth S.toShadow
  refine ⟨n, ?_⟩
  change (initialImageShadow n).map.ker ≤ S.map.ker
  exact ker_factors_through
    (initialImageShadow n).map
    S.map
    (D.uniquely_through_target
      S.toShadow
      le_rfl).exists

/--
The honest finite kernel-image quotient shadows form a kernel-cofinal finite
`3` quotient family of the actual initial Galois group.
-/
lemma initial_shadow_cofinal
    (D : KRData) :
    CofinalShadowFamily
      initialKochShadow := by
  exact D.initial_koch_three

/--
The subgroup invisible to every honest finite kernel-image quotient shadow of
the actual initial Galois group.
-/
def InitialShadowFamily :
    Subgroup initialGaloisGroup :=
  shadowFamilyKernel initialKochShadow

/--
Honest finite kernel-image quotient shadows detect exactly the full finite
`3` residual kernel of the actual initial Galois group.
-/
lemma initial_shadow_residual
    (D : KRData) :
    InitialShadowFamily =
      residualKernel 3 initialGaloisGroup := by
  exact shadow_family_cofinal
    initialKochShadow
    D.initial_shadow_cofinal

/--
Because the actual initial Galois group is residually finite `3`, the honest
finite kernel-image quotient shadows have trivial common kernel.
-/
lemma initial_shadow_bot
    (D : KRData) :
    InitialShadowFamily = ⊥ := by
  rw [D.initial_shadow_residual]
  exact initial_galois_residually

/--
Package one corrected canonical finite defect stage as an actual surjective
finite `3`-group quotient of the actual initial Galois group.
-/
def canonicalDefectShadow
    (D : KRData)
    (n : ℕ) :
    InitialKochQuotient where
  toShadow := D.kochDefectShadow n
  map_surjective := D.defect_shadow_surjective n

/--
The corrected canonical finite defect quotient shadow map is its named quotient
factor from the actual initial Galois group.
-/
@[simp]
lemma koch_defect_shadow
    (D : KRData)
    (n : ℕ) :
    (D.canonicalDefectShadow n).map =
      D.canonicalDefectFactor n := rfl

/--
Every actual finite `3`-group quotient of the actual initial Galois group lies
above one corrected canonical finite defect quotient shadow.
-/
lemma canonical_defect_shadow
    (D : KRData)
    (S : InitialKochQuotient) :
    ∃ n : ℕ,
      (D.canonicalDefectShadow n).map.ker ≤
        S.map.ker := by
  rcases D.initial_koch_three
      S with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  change (D.kochDefectShadow n).map.ker ≤ S.map.ker
  rw [D.defect_shadow_image]
  exact hn

/--
The corrected canonical finite defect quotient shadows form a kernel-cofinal
finite `3` quotient family of the actual initial Galois group.
-/
lemma defect_shadow_cofinal
    (D : KRData) :
    CofinalShadowFamily
      D.canonicalDefectShadow := by
  exact D.canonical_defect_shadow

/--
The subgroup invisible to every corrected canonical finite defect quotient
shadow of the actual initial Galois group.
-/
def CanonicalDefectShadow
    (D : KRData) :
    Subgroup initialGaloisGroup :=
  shadowFamilyKernel D.canonicalDefectShadow

/--
Corrected canonical finite defect quotient shadows detect exactly the full
finite `3` residual kernel of the actual initial Galois group.
-/
lemma defect_shadow_residual
    (D : KRData) :
    D.CanonicalDefectShadow =
      residualKernel 3 initialGaloisGroup := by
  exact shadow_family_cofinal
    D.canonicalDefectShadow
    D.defect_shadow_cofinal

/--
Because the actual initial Galois group is residually finite `3`, the corrected
canonical finite defect quotient shadows have trivial common kernel.
-/
lemma defect_shadow_bot
    (D : KRData) :
    D.CanonicalDefectShadow = ⊥ := by
  rw [D.defect_shadow_residual]
  exact initial_galois_residually

/--
Under the desired theorem, package one raw canonical Zassenhaus finite relator
quotient as the descended actual finite `3` quotient of the actual initial
Galois group.
-/
def descendedShadowTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    InitialKochQuotient :=
  D.relatorDescendTheorem hfactor
    (D.ZassenhausRelatorQuotient n)

/--
The descended raw canonical Zassenhaus finite relator quotient pulls back to
its original raw relator quotient map from the initial free pro-`3` group.
-/
lemma descended_shadow_theorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (n : ℕ) :
    (D.descendedShadowTheorem
      hfactor n).map.comp initialKochQuotient =
      (D.ZassenhausRelatorQuotient n).map := by
  exact D.descend_theorem_comp
    hfactor
    (D.ZassenhausRelatorQuotient n)

/--
Under the desired theorem, every actual finite `3`-group quotient of the actual
initial Galois group lies above one descended raw canonical Zassenhaus finite
relator quotient.
-/
lemma zassenhaus_fin_koch
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem)
    (S : InitialKochQuotient) :
    ∃ n : ℕ,
      (D.descendedShadowTheorem
        hfactor n).map.ker ≤
        S.map.ker := by
  let T : D.ThreeRelatorQuotient :=
    D.initialKochPullback S
  rcases D.zassenhaus_relator_kernel
      T with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro y hy
  rcases initial_quotient_surjective y with ⟨x, rfl⟩
  apply MonoidHom.mem_ker.mpr
  have hdesc := DFunLike.congr_fun
    (D.descended_shadow_theorem
      hfactor
      n)
    x
  have hxraw :
      x ∈ (D.ZassenhausRelatorQuotient n).map.ker := by
    apply MonoidHom.mem_ker.mpr
    change (D.ZassenhausRelatorQuotient n).map x = 1
    change (D.descendedShadowTheorem
        hfactor n).map
        (initialKochQuotient x) =
      (D.ZassenhausRelatorQuotient n).map x at hdesc
    exact hdesc.symm.trans (MonoidHom.mem_ker.mp hy)
  have hxT : x ∈ T.map.ker := hn hxraw
  have hpullback := DFunLike.congr_fun
    (D.initial_three_pullback S)
    x
  change T.map x = S.map (initialKochQuotient x) at hpullback
  exact hpullback.symm.trans (MonoidHom.mem_ker.mp hxT)

/--
Under the desired theorem, descended raw canonical Zassenhaus finite relator
quotients form a kernel-cofinal finite `3` quotient family of the actual
initial Galois group.
-/
lemma descended_shadow_cofinal
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    CofinalShadowFamily
      (D.descendedShadowTheorem
        hfactor) := by
  exact D.zassenhaus_fin_koch
    hfactor

/--
Under the desired theorem, the subgroup invisible to every descended raw
canonical Zassenhaus finite relator quotient of the actual initial Galois
group.
-/
def DescendedShadowTheorem
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    Subgroup initialGaloisGroup :=
  shadowFamilyKernel
    (D.descendedShadowTheorem
      hfactor)

/--
Under the desired theorem, descended raw canonical Zassenhaus finite relator
quotients detect exactly the full finite `3` residual kernel of the actual
initial Galois group.
-/
lemma fin_residual_kernel
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.DescendedShadowTheorem
        hfactor =
      residualKernel 3 initialGaloisGroup := by
  exact shadow_family_cofinal
    (D.descendedShadowTheorem
      hfactor)
    (D.descended_shadow_cofinal
      hfactor)

/--
Under the desired theorem, descended raw canonical Zassenhaus finite relator
quotients have trivial common kernel in the actual initial Galois group.
-/
lemma descended_shadow_bot
    (D : KRData)
    (hfactor : D.KochFactorizationTheorem) :
    D.DescendedShadowTheorem
        hfactor = ⊥ := by
  rw [D.fin_residual_kernel
    hfactor]
  exact initial_galois_residually

end KRData

end TBluepr
end Submission
