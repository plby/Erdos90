import Submission.ClassField.Shifting.CyclicCupPeriodicity
import Submission.ClassField.ReciprocityExistence.CharacterBoundary

/-!
# The normalized class in cyclic Tate cup-periodicity

This file identifies the degree-two class constructed from the standard
cyclic resolution with Milne's normalized character boundary.  Together
with `Remark35CyclicCupPeriodicity`, this gives Proposition II.3.4 and
Remark II.3.5 with the normalization stated in `CFT.tex`.
-/

namespace Submission.CField.RExist

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep Representation
open Submission.CField.Shifting
open Submission.CField.LRecip
open Submission.CField.TCohomo
open Submission.CField.COps.CPBuild
open scoped MonoidalCategory TensorProduct

noncomputable section

variable {G : Type} [CommGroup G] [Fintype G]

private noncomputable def normalizedIntegerCharacter
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Additive G →+ rationalModIntegers :=
  characterRationalIntegers G
    (multiplicativeRationalCharacter G g hg)

/-- Extend the normalized character coefficientwise from `G` to `ℤ[G]`. -/
private noncomputable def cyclicCharacterSum
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    IntegralGroupRing G →ₗ[ℤ] rationalModIntegers :=
  Finsupp.linearCombination ℤ
    (fun h : G ↦ normalizedIntegerCharacter g hg (Additive.ofMul h))

private theorem cyclic_character_single
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (h : G) (z : ℤ) :
    cyclicCharacterSum g hg (MonoidAlgebra.single h z) =
      z • normalizedIntegerCharacter g hg (Additive.ofMul h) := by
  change (Finsupp.linearCombination ℤ
      (fun h : G ↦ normalizedIntegerCharacter g hg (Additive.ofMul h)))
        (Finsupp.single h z) = _
  rw [Finsupp.linearCombination_single]

/-- Translation of a coefficient-weighted character sum introduces the
augmentation times the translating character. -/
private theorem cyclic_character_action
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (k : G) (x : IntegralGroupRing G) :
    cyclicCharacterSum g hg ((Rep.leftRegular ℤ G).ρ k x) =
      augmentation G x •
          normalizedIntegerCharacter g hg (Additive.ofMul k) +
        cyclicCharacterSum g hg x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      calc
        cyclicCharacterSum g hg
            ((Rep.leftRegular ℤ G).ρ k 0) =
            cyclicCharacterSum g hg 0 :=
          congrArg _ (map_zero ((Rep.leftRegular ℤ G).ρ k))
        _ = 0 := map_zero _
        _ = augmentation G 0 •
              normalizedIntegerCharacter g hg (Additive.ofMul k) +
            cyclicCharacterSum g hg 0 := by
          rw [map_zero (augmentation G), zero_smul, map_zero, zero_add]
  | add x y hx hy =>
      calc
        cyclicCharacterSum g hg
            ((Rep.leftRegular ℤ G).ρ k (x + y)) =
            cyclicCharacterSum g hg
              ((Rep.leftRegular ℤ G).ρ k x +
                (Rep.leftRegular ℤ G).ρ k y) :=
          congrArg _ (map_add ((Rep.leftRegular ℤ G).ρ k) x y)
        _ = cyclicCharacterSum g hg
              ((Rep.leftRegular ℤ G).ρ k x) +
            cyclicCharacterSum g hg
              ((Rep.leftRegular ℤ G).ρ k y) := map_add _ _ _
        _ = augmentation G (x + y) •
              normalizedIntegerCharacter g hg (Additive.ofMul k) +
            cyclicCharacterSum g hg (x + y) := by
          rw [hx, hy, map_add (augmentation G), map_add, add_smul]
          abel
  | single h z =>
      rw [Representation.ofMulAction_single,
        cyclic_character_single,
        cyclic_character_single, augmentation_single]
      change z • normalizedIntegerCharacter g hg
          (Additive.ofMul (k * h)) = _
      rw [show Additive.ofMul (k * h) =
          Additive.ofMul k + Additive.ofMul h by rfl, map_add]
      exact smul_add z _ _

/-- The normalized character, extended to the augmentation ideal.  It is
equivariant because the augmentation error in translation vanishes there. -/
private noncomputable def cyclicAugmentationCharacter
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    augmentationIdealRep (G := G) ⟶
      Rep.trivial ℤ G rationalModIntegers :=
  Rep.ofHom
    { toLinearMap := (cyclicCharacterSum g hg).comp
        (augmentationIdeal G).subtype
      isIntertwining' := fun k ↦ by
        apply LinearMap.ext
        intro x
        change cyclicCharacterSum g hg
            (augmentationLeftAction k x).1 =
          cyclicCharacterSum g hg x.1
        have hact := cyclic_character_action g hg k x.1
        rw [regular_int_action] at hact
        rw [LinearMap.mem_ker.mp x.2, zero_smul, zero_add] at hact
        simpa only [augmentation_action_coe] using hact }

/-- The middle vertical map from the cyclic resolution to
`0 → ℤ → ℚ → ℚ/ℤ → 0`: augmentation divided by `|G|`. -/
private noncomputable def cyclicAverageRational :
    Rep.leftRegular ℤ G ⟶ Rep.trivial ℤ G ℚ :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x ↦ (augmentation G x : ℚ) / Nat.card G
          map_add' := by
            intro x y
            rw [show augmentation G (x + y) =
                augmentation G x + augmentation G y by
              exact map_add (augmentation G) x y]
            rw [Int.cast_add, add_div]
          map_smul' := by
            intro z x
            rw [show augmentation G (z • x) = z • augmentation G x by
              exact (augmentation G).map_smul z x]
            change ((z * augmentation G x : ℤ) : ℚ) / Nat.card G = _
            rw [Int.cast_mul]
            change ((z : ℤ) : ℚ) * (augmentation G x : ℚ) /
              Nat.card G = (z : ℚ) *
                ((augmentation G x : ℚ) / Nat.card G)
            ring }
      isIntertwining' := fun k ↦ by
        apply LinearMap.ext
        intro x
        dsimp only [LinearMap.comp_apply, Representation.trivial_apply]
        change
          (augmentation G ((Representation.ofMulAction ℤ G G) k x) : ℚ) /
              Nat.card G =
          (augmentation G x : ℚ) /
            Nat.card G
        rw [augmentation_regular_action] }

private theorem normalized_character_generator
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    normalizedIntegerCharacter g hg (Additive.ofMul g) =
      (rationalIntegers G).hom ((Nat.card G : ℚ)⁻¹) := by
  apply rationalIntegersInvariant.injective
  change rationalIntegersInvariant
      (rationalIntegersInvariant.symm
        (multiplicativeRationalCharacter G g hg
          (Additive.ofMul g))) =
    rationalIntegersInvariant
      (Submodule.Quotient.mk ((Nat.card G : ℚ)⁻¹))
  rw [AddEquiv.apply_symm_apply,
    rational_integers_mk,
    multiplicative_rational_character]

private theorem cyclic_average_element
    (g : G) (_hg : ∀ x : G, x ∈ Subgroup.zpowers g) (z : ℤ) :
    cyclicAverageRational
        (cyclicNormInclusion (G := G) z) =
      (integerToRational G).hom z := by
  change (augmentation G (cyclicNormElement (G := G) z) : ℚ) /
      Nat.card G = z
  have hcard : Fintype.card G = Nat.card G := Nat.card_eq_fintype_card.symm
  rw [show augmentation G (cyclicNormElement (G := G) z) =
      Fintype.card G * z by
    change augmentation G
      (Finsupp.equivFunOnFinite.symm (fun _ : G ↦ z)) = _
    rw [Finsupp.equivFunOnFinite_symm_eq_sum]
    calc
      augmentation G (∑ a : G, Finsupp.single a z) =
          ∑ a : G, augmentation G (Finsupp.single a z) :=
        by simp
      _ = Fintype.card G * z := by simp]
  rw [hcard]
  have hne : (Nat.card G : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [Int.cast_mul, Int.cast_natCast]
  field_simp

private theorem cyclicAverage_difference
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (x : IntegralGroupRing G) :
    (rationalIntegers G).hom (cyclicAverageRational x) =
      cyclicAugmentationCharacter g hg
        (cyclicDifferenceIdeal g x) := by
  change (rationalIntegers G).hom
      ((augmentation G x : ℚ) / Nat.card G) =
    cyclicCharacterSum g hg
      (cyclicDifferenceIdeal g x).1
  rw [cyclic_difference_coe]
  dsimp only [Rep.sub_hom, Rep.applyAsHom]
  change (rationalIntegers G).hom
      ((augmentation G x : ℚ) / Nat.card G) =
    cyclicCharacterSum g hg
      ((Rep.applyAsHom (Rep.leftRegular ℤ G) g).hom x -
        ((𝟙 (Rep.leftRegular ℤ G) :
          Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G).hom x))
  have hsub :
      ((Rep.applyAsHom (Rep.leftRegular ℤ G) g).hom x -
          ((𝟙 (Rep.leftRegular ℤ G) :
            Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G).hom x) :
        Rep.leftRegular ℤ G) =
      ((show IntegralGroupRing G from (Rep.leftRegular ℤ G).ρ g x) - x :
        IntegralGroupRing G) := by
    rfl
  rw [hsub, (cyclicCharacterSum g hg).map_sub]
  change (rationalIntegers G).hom
      ((augmentation G x : ℚ) / Nat.card G) =
    cyclicCharacterSum g hg
        ((Rep.leftRegular ℤ G).ρ g x) -
      cyclicCharacterSum g hg x
  rw [cyclic_character_action]
  abel_nf
  rw [normalized_character_generator]
  have hcard : (Nat.card G : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [show (augmentation G x : ℚ) / Nat.card G =
      (augmentation G x : ℤ) • (Nat.card G : ℚ)⁻¹ by
    rw [← Int.cast_smul_eq_zsmul ℚ]
    change (augmentation G x : ℚ) / Nat.card G =
      (augmentation G x : ℚ) * (Nat.card G : ℚ)⁻¹
    rw [div_eq_mul_inv]]
  exact (map_zsmul (rationalIntegers G).hom
    (augmentation G x) (Nat.card G : ℚ)⁻¹).symm

/-- A morphism from the first cyclic short exact sequence to the rational
coefficient sequence, normalized to be the identity on `ℤ`. -/
private noncomputable def cyclicResolutionSequence
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    cyclicDifferenceSequence g ⟶ integerRationalSequence G where
  τ₁ := 𝟙 _
  τ₂ := cyclicAverageRational
  τ₃ := cyclicAugmentationCharacter g hg
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    exact (cyclic_average_element g hg z).symm
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact cyclicAverage_difference g hg x

private theorem cyclic_character_class
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (h : G) :
    cyclicAugmentationCharacter g hg (augmentationClass G h) =
      normalizedIntegerCharacter g hg (Additive.ofMul h) := by
  change cyclicCharacterSum g hg
      (MonoidAlgebra.single h 1 - MonoidAlgebra.single 1 1) = _
  rw [(cyclicCharacterSum g hg).map_sub,
    cyclic_character_single,
    cyclic_character_single, one_smul, one_smul]
  change normalizedIntegerCharacter g hg (Additive.ofMul h) -
      normalizedIntegerCharacter g hg 0 = _
  rw [map_zero, sub_zero]

private theorem boundary_normalized_character
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    groupCohomology.map (MonoidHom.id G)
        (cyclicAugmentationCharacter g hg) 1
        (groupCohomology.δ (augmentation_short_exact (G := G))
          0 1 rfl integralUnit) =
      groupCohomology.H1π (Rep.trivial ℤ G rationalModIntegers)
        ((groupCohomology.cocycles₁IsoOfIsTrivial
          (Rep.trivial ℤ G rationalModIntegers)).inv
            (normalizedIntegerCharacter g hg)) := by
  rw [boundary_integral_unit]
  have hmap := congrArg
    (fun f ↦ f (augmentationCocycle (G := G)))
    (groupCohomology.H1π_comp_map (MonoidHom.id G)
      (cyclicAugmentationCharacter g hg))
  simp only [ConcreteCategory.comp_apply] at hmap
  calc
    _ = groupCohomology.H1π (Rep.trivial ℤ G rationalModIntegers)
        (groupCohomology.mapCocycles₁ (MonoidHom.id G)
          (cyclicAugmentationCharacter g hg)
          (augmentationCocycle (G := G))) := hmap
    _ = _ := by
      apply congrArg
        (groupCohomology.H1π (Rep.trivial ℤ G rationalModIntegers))
      apply groupCohomology.cocycles₁_ext
      intro h
      exact cyclic_character_class g hg h

private theorem resolution_delta_naturality
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (b : groupCohomology (augmentationIdealRep (G := G)) 1) :
    groupCohomology.δ (difference_short_exact g hg)
        1 2 rfl b =
      groupCohomology.δ (sequence_short_exact G)
        1 2 rfl
        (groupCohomology.map (MonoidHom.id G)
          (cyclicAugmentationCharacter g hg) 1 b) := by
  let f := cyclicResolutionSequence g hg
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    ((groupCohomology.cochainsFunctor ℤ G).mapShortComplex.map f)
    (groupCohomology.map_cochainsFunctor_shortExact
      (difference_short_exact g hg))
    (groupCohomology.map_cochainsFunctor_shortExact
      (sequence_short_exact G)) 1 2 rfl
  have hnat' :
      groupCohomology.δ (difference_short_exact g hg)
          1 2 rfl ≫
        groupCohomology.map (MonoidHom.id G)
          (𝟙 (Rep.trivial ℤ G ℤ)) 2 =
      groupCohomology.map (MonoidHom.id G)
          (cyclicAugmentationCharacter g hg) 1 ≫
        groupCohomology.δ (sequence_short_exact G)
          1 2 rfl := by
    simpa [f, cyclicResolutionSequence] using hnat
  have happ := congrArg (fun q ↦ q b) hnat'
  simp only [ConcreteCategory.comp_apply] at happ
  have hid : groupCohomology.map (MonoidHom.id G)
      (𝟙 (Rep.trivial ℤ G ℤ)) 2
      (groupCohomology.δ (difference_short_exact g hg)
        1 2 rfl b) =
      groupCohomology.δ (difference_short_exact g hg)
        1 2 rfl b := by
    have hmap := groupCohomology.map_id
      (G := G) (B := Rep.trivial ℤ G ℤ) (n := 2)
    simpa only [ConcreteCategory.id_apply] using congrArg
      (fun q ↦ q (groupCohomology.δ
        (difference_short_exact g hg) 1 2 rfl b)) hmap
  simpa only [ConcreteCategory.comp_apply, hid] using happ

/-- **Remark II.3.5, normalization.**  The period class constructed from
the cyclic resolution is precisely the class corresponding under
`H²(G,ℤ) ≃ Hom(G,ℚ/ℤ)` to the character that sends the chosen
generator to `1 / |G|`. -/
theorem cyclic_periodicity_boundary
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    cyclicPeriodicityClass g hg =
      characterBoundary G
        (multiplicativeRationalCharacter G g hg) := by
  let b := groupCohomology.δ (augmentation_short_exact (G := G))
    0 1 rfl integralUnit
  change groupCohomology.δ
      (difference_short_exact g hg) 1 2 rfl b = _
  rw [resolution_delta_naturality g hg b]
  dsimp only [b]
  have hb := congrArg
    (groupCohomology.δ (sequence_short_exact G)
      1 2 rfl)
    (boundary_normalized_character g hg)
  have hc := (character_boundary_connecting G
    (multiplicativeRationalCharacter G g hg)).symm
  exact hb.trans (by
    simpa [normalizedIntegerCharacter] using hc)

/-- In every positive degree, cyclic periodicity is cup product with the
character-boundary class normalized by `g ↦ 1 / |G|`. -/
theorem cup_periodicity_normalized
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : 0 < n) (a : groupCohomology A n) :
    cyclicCupPeriodicity A g hg n hn a =
      groupCohomology.map (MonoidHom.id G) (ρ_ A).hom (n + 2)
        (cupCohomology A (Rep.trivial ℤ G ℤ) n 2 a
          (characterBoundary G
            (multiplicativeRationalCharacter G g hg))) := by
  rw [← cyclic_periodicity_boundary g hg]
  exact cyclic_cup_periodicity A g hg n hn a

/-- At Tate degree zero, the all-range cyclic shift is cup product with the
same normalized character-boundary class, on invariant representatives. -/
theorem shift_projection_normalized
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : groupCohomology A 0) :
    (cyclicTateShift A g hg).zero
        (tateCohomologyProjection A
          ((groupCohomology.H0Iso A).hom a)) =
      groupCohomology.map (MonoidHom.id G) (ρ_ A).hom 2
        (cupCohomology A (Rep.trivial ℤ G ℤ) 0 2 a
          (characterBoundary G
            (multiplicativeRationalCharacter G g hg))) := by
  rw [← cyclic_periodicity_boundary g hg]
  exact cyclic_shift_projection A g hg a

end

end Submission.CField.RExist
