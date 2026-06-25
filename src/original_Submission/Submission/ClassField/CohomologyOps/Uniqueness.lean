import Submission.ClassField.CohomologyOps.Connecting
import Submission.ClassField.CohomologyOps.DeltaRight
import Submission.ClassField.CohomologyOps.TensorExact

namespace Submission.CField.COps.CPBuild

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalCategory

variable {G : Type} [Group G]

/-- A family of bi-additive candidate cup products in all bidegrees. -/
abbrev CPFam :=
  ∀ (M N : Rep ℤ G) (r s : ℕ),
    groupCohomology M r →ₗ[ℤ]
      groupCohomology N s →ₗ[ℤ] groupCohomology (M ⊗ N : Rep ℤ G) (r + s)

def NaturalInCoefficients (P : CPFam (G := G)) : Prop :=
  ∀ {M N M' N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N')
    (r s : ℕ) (a : groupCohomology M r) (b : groupCohomology N s),
    groupCohomology.map (MonoidHom.id G) (f ⊗ₘ g) (r + s)
        (P M N r s a b) =
      P M' N' r s
        (groupCohomology.map (MonoidHom.id G) f r a)
        (groupCohomology.map (MonoidHom.id G) g s b)

def DegreeZeroNormalized (P : CPFam (G := G)) : Prop :=
  ∀ (M N : Rep ℤ G) (a : groupCohomology.cocycles M 0)
    (b : groupCohomology.cocycles N 0),
    P M N 0 0 (groupCohomology.π M 0 a) (groupCohomology.π N 0 b) =
      groupCohomology.π (M ⊗ N : Rep ℤ G) 0 (cupCocycle M N 0 0 a b)

def CompatibleLeftConnecting (P : CPFam (G := G)) : Prop :=
  ∀ (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact)
    (N : Rep ℤ G)
    (hXN : (X.map ((tensoringRight (Rep ℤ G)).obj N)).ShortExact)
    (i s : ℕ) (a : groupCohomology X.X₃ i) (b : groupCohomology N s),
    groupCohomology.δ hXN (i + s) ((i + s) + 1) rfl
        (P X.X₃ N i s a b) =
      cohomologyCast (X.X₁ ⊗ N : Rep ℤ G)
        (by omega : (i + 1) + s = (i + s) + 1)
        (P X.X₁ N (i + 1) s
          (groupCohomology.δ hX i (i + 1) rfl a) b)

def CompatibleRightConnecting (P : CPFam (G := G)) : Prop :=
  ∀ (M : Rep ℤ G) (X : ShortComplex (Rep ℤ G)) (hX : X.ShortExact)
    (hMX : (X.map ((tensoringLeft (Rep ℤ G)).obj M)).ShortExact)
    (r s : ℕ) (a : groupCohomology M r) (b : groupCohomology X.X₃ s),
    P M X.X₁ r (s + 1) a (groupCohomology.δ hX s (s + 1) rfl b) =
      (-1 : ℤ) ^ r • groupCohomology.δ hMX (r + s) ((r + s) + 1) rfl
        (P M X.X₃ r s a b)

theorem cohomologyCast_injective (A : Rep ℤ G) {m n : ℕ} (h : m = n) :
    Function.Injective (cohomologyCast A h) := by
  subst h
  intro x y hxy
  exact hxy

theorem CPFam.pointwise_unique
    (P Q : CPFam (G := G))
    (hP0 : DegreeZeroNormalized P) (hQ0 : DegreeZeroNormalized Q)
    (hPL : CompatibleLeftConnecting P)
    (hQL : CompatibleLeftConnecting Q)
    (hPR : CompatibleRightConnecting P)
    (hQR : CompatibleRightConnecting Q) :
    ∀ (r s : ℕ) (M N : Rep ℤ G)
      (a : groupCohomology M r) (b : groupCohomology N s),
      P M N r s a b = Q M N r s a b := by
  intro r
  induction r with
  | zero =>
      intro s
      induction s with
      | zero =>
          intro M N a b
          induction a using groupCohomology_induction_on with
          | h ac =>
              induction b using groupCohomology_induction_on with
              | h bc => rw [hP0, hQ0]
      | succ s ih =>
          intro M N a b
          let X := dimensionShiftSequence N
          let hX : X.ShortExact := shift_sequence_short N
          let hMX : (X.map ((tensoringLeft (Rep ℤ G)).obj M)).ShortExact :=
            tensor_shift_short M N
          let δN := groupCohomology.δ hX s (s + 1) rfl
          letI : Epi δN := groupCohomology.epi_δ_of_isZero hX s
            (shift_middle_acyclic N (s + 1) (Nat.succ_pos s))
          obtain ⟨b', hb'⟩ := (ModuleCat.epi_iff_surjective δN).1 inferInstance b
          rw [← hb']
          change P M X.X₁ 0 (s + 1) a
              (groupCohomology.δ hX s (s + 1) rfl b') =
            Q M X.X₁ 0 (s + 1) a
              (groupCohomology.δ hX s (s + 1) rfl b')
          rw [hPR M X hX hMX 0 s a b', hQR M X hX hMX 0 s a b']
          simp only [pow_zero, one_smul]
          rw [ih M X.X₃ a b']
      
  | succ r ih =>
      intro s M N a b
      let X := dimensionShiftSequence M
      let hX : X.ShortExact := shift_sequence_short M
      let hXN : (X.map ((tensoringRight (Rep ℤ G)).obj N)).ShortExact :=
        shift_short_exact M N
      let δM := groupCohomology.δ hX r (r + 1) rfl
      letI : Epi δM := groupCohomology.epi_δ_of_isZero hX r
        (shift_middle_acyclic M (r + 1) (Nat.succ_pos r))
      obtain ⟨a', ha'⟩ := (ModuleCat.epi_iff_surjective δM).1 inferInstance a
      rw [← ha']
      have hP := hPL X hX N hXN r s a' b
      have hQ := hQL X hX N hXN r s a' b
      rw [ih s X.X₃ N a' b] at hP
      have hc := hP.symm.trans hQ
      exact cohomologyCast_injective (X.X₁ ⊗ N : Rep ℤ G)
        (by omega : (r + 1) + s = (r + s) + 1) hc

/-- The explicit cup product constructed from inhomogeneous cocycles, viewed
as one family in all bidegrees. -/
noncomputable def canonicalCupFamily : CPFam (G := G) :=
  fun M N r s ↦ cupCohomology M N r s

theorem canonical_cup_zero :
    DegreeZeroNormalized (canonicalCupFamily (G := G)) := by
  intro M N a b
  exact cupCohomology_π M N 0 0 a b

theorem canonical_cup_natural :
    NaturalInCoefficients (canonicalCupFamily (G := G)) := by
  intro M N M' N' f g r s a b
  exact cupCohomology_natural f g r s a b

theorem cup_family_connecting :
    CompatibleLeftConnecting (canonicalCupFamily (G := G)) := by
  intro X hX N hXN i s a b
  exact connecting_cup X hX N hXN i s a b

theorem canonical_cup_connecting :
    CompatibleRightConnecting (canonicalCupFamily (G := G)) := by
  intro M X hX hMX r s a b
  exact cup_cohomology_delta M hX hMX r s a b

/-- Proposition II.1.38, uniqueness: conditions (b)--(d) already determine
the family. Naturality (a) is therefore not needed as an extra uniqueness
hypothesis. -/
theorem CPFam.eq_canonical
    (P : CPFam (G := G))
    (hP0 : DegreeZeroNormalized P)
    (hPL : CompatibleLeftConnecting P)
    (hPR : CompatibleRightConnecting P) :
    P = canonicalCupFamily (G := G) := by
  funext M N r s
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  exact CPFam.pointwise_unique P canonicalCupFamily
    hP0 canonical_cup_zero hPL
    cup_family_connecting hPR
    canonical_cup_connecting r s M N a b

/-- Proposition II.1.38, existence and uniqueness of the cup-product family
under its degree-zero normalization and both connecting-map laws. -/
theorem unique_cup_family :
    ∃! P : CPFam (G := G),
      NaturalInCoefficients P ∧
        DegreeZeroNormalized P ∧
        CompatibleLeftConnecting P ∧
        CompatibleRightConnecting P := by
  refine ⟨canonicalCupFamily,
    ⟨canonical_cup_natural,
      canonical_cup_zero,
      cup_family_connecting,
      canonical_cup_connecting⟩, ?_⟩
  intro P hP
  exact CPFam.eq_canonical P hP.2.1 hP.2.2.1 hP.2.2.2

end Submission.CField.COps.CPBuild
