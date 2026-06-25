import Towers.ClassField.CohomologyOps.Uniqueness
import Towers.ClassField.CohomologyOps.DeltaRight
import Towers.ClassField.Shifting.TensorExact
import Towers.ClassField.Shifting.DoubleShift
import Mathlib.Algebra.Homology.HomologySequenceLemmas

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep
open Towers.CField.COps.CPBuild
open Towers.CField.TCohomo
open groupCohomology
open scoped MonoidalCategory TensorProduct

noncomputable section

variable {G : Type} [Group G]

noncomputable def integralUnitCocycle :
    groupCohomology.cocycles (Rep.trivial ℤ G ℤ) 0 :=
  (groupCohomology.cocyclesIso₀ (Rep.trivial ℤ G ℤ)).inv
    ⟨(1 : ℤ), by intro g; rfl⟩

noncomputable def integralUnit :
    groupCohomology (Rep.trivial ℤ G ℤ) 0 :=
  groupCohomology.π _ 0 integralUnitCocycle

/-- The cocycle `g ↦ g - 1` with values in the augmentation ideal. -/
noncomputable def augmentationCocycle :
    groupCohomology.cocycles₁ (augmentationIdealRep (G := G)) :=
  ⟨fun g ↦ augmentationClass G g,
    (groupCohomology.mem_cocycles₁_iff _).2 fun g h ↦ by
      change augmentationClass G (g * h) =
        augmentationLeftAction g (augmentationClass G h) +
          augmentationClass G g
      rw [augmentation_action_class]
      simp⟩

theorem boundary_integral_unit :
    groupCohomology.δ (augmentation_short_exact (G := G))
        0 1 rfl integralUnit =
      groupCohomology.H1π _ (augmentationCocycle (G := G)) := by
  let X := augmentationSequence (G := G)
  let z : X.X₃.ρ.invariants := ⟨(1 : ℤ), by intro g; rfl⟩
  let y : X.X₂ := (MonoidAlgebra.single 1 1 : IntegralGroupRing G)
  let x : G → X.X₁ := fun g ↦ augmentationClass G g
  have hy : X.g.hom y = z := by
    change augmentation G
      (MonoidAlgebra.single 1 1 : IntegralGroupRing G) = (1 : ℤ)
    exact augmentation_one G
  have hx : X.f.hom ∘ x = groupCohomology.d₀₁ X.X₂ y := by
    funext g
    dsimp [X, x, y, augmentationSequence, groupCohomology.d₀₁,
      augmentationIdealInclusion]
    change
      (augmentationIdeal G).subtype (augmentationClass G g) =
        (show IntegralGroupRing G from
          (Rep.leftRegular ℤ G).ρ g
            (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) -
          (MonoidAlgebra.single 1 1 : IntegralGroupRing G)
    rw [Representation.ofMulAction_single]
    simpa only [smul_eq_mul, mul_one] using
      augmentationClass_coe (G := G) g
  have hboundary := groupCohomology.δ₀_apply
    (augmentation_short_exact (G := G)) z y hy x hx
  simpa [integralUnit, integralUnitCocycle, X, z, x, augmentationCocycle,
    groupCohomology.H0Iso] using hboundary

theorem splitting_boundary_cocycle
    (C : Rep ℤ G) (gamma : groupCohomology C 2) :
    let φ := normalizedCocycleClass C gamma
    let hφ := normalized_cocycle_class C gamma
    groupCohomology.δ (splitting_sequence_short C φ hφ)
        1 2 rfl (groupCohomology.H1π _ (augmentationCocycle (G := G))) =
      gamma := by
  dsimp only
  let φ := normalizedCocycleClass C gamma
  let hφ := normalized_cocycle_class C gamma
  let X := splittingModuleSequence C φ hφ
  let y : G → X.X₂ := fun g ↦ (0, augmentationClass G g)
  let x : G × G → X.X₁ := fun p ↦ φ p
  have hy : X.g.hom ∘ y = augmentationCocycle (G := G) := by
    funext g
    rfl
  have hx : X.f.hom ∘ x = groupCohomology.d₁₂ X.X₂ y := by
    funext p
    change (φ p, 0) = _
    simpa [X, y, x] using
      (congrFun (splittingCochain_coboundary C φ hφ) p).symm
  calc
    _ = groupCohomology.H2π C φ := by
      simpa [X, φ, hφ, x] using
        groupCohomology.δ₁_apply
          (splitting_sequence_short C φ hφ)
          (augmentationCocycle (G := G)) y hy x hx
    _ = gamma := normalized_cocycle_represents C gamma

noncomputable def unitorShortComplex
    (X : ShortComplex (Rep ℤ G)) :
    leftShortComplex (Rep.trivial ℤ G ℤ) X ⟶ X where
  τ₁ := (λ_ X.X₁).hom
  τ₂ := (λ_ X.X₂).hom
  τ₃ := (λ_ X.X₃).hom
  comm₁₂ := (MonoidalCategory.leftUnitor_naturality X.f).symm
  comm₂₃ := (MonoidalCategory.leftUnitor_naturality X.g).symm

theorem left_unitor_naturality
    (X : ShortComplex (Rep ℤ G))
    (hZX : (leftShortComplex (Rep.trivial ℤ G ℤ) X).ShortExact)
    (hX : X.ShortExact) (n : ℕ) :
    groupCohomology.δ hZX n (n + 1) rfl ≫
        groupCohomology.map (MonoidHom.id G) (λ_ X.X₁).hom (n + 1) =
      groupCohomology.map (MonoidHom.id G) (λ_ X.X₃).hom n ≫
        groupCohomology.δ hX n (n + 1) rfl := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    ((groupCohomology.cochainsFunctor ℤ G).mapShortComplex.map
      (unitorShortComplex X))
    (groupCohomology.map_cochainsFunctor_shortExact hZX)
    (groupCohomology.map_cochainsFunctor_shortExact hX) n (n + 1) rfl

theorem unitor_delta_naturality
    (X : ShortComplex (Rep ℤ G))
    (hZX : (leftShortComplex (Rep.trivial ℤ G ℤ) X).ShortExact)
    (hX : X.ShortExact) (n : ℕ)
    (z : groupCohomology
      (leftShortComplex (Rep.trivial ℤ G ℤ) X).X₃ n) :
    groupCohomology.map (MonoidHom.id G) (λ_ X.X₁).hom (n + 1)
        (groupCohomology.δ hZX n (n + 1) rfl z) =
      groupCohomology.δ hX n (n + 1) rfl
        (groupCohomology.map (MonoidHom.id G) (λ_ X.X₃).hom n z) := by
  have h := congrArg (fun f ↦ f z)
    (left_unitor_naturality X hZX hX n)
  simpa only [ConcreteCategory.comp_apply] using h

theorem cup_integral_right (n : ℕ)
    (x : groupCohomology (Rep.trivial ℤ G ℤ) n) :
    groupCohomology.map (MonoidHom.id G)
        (λ_ (Rep.trivial ℤ G ℤ)).hom n
        (cupCohomology (Rep.trivial ℤ G ℤ) (Rep.trivial ℤ G ℤ)
          n 0 x integralUnit) = x := by
  induction x using groupCohomology_induction_on with
  | h xc =>
      rw [integralUnit, cupCohomology_π]
      simp only [Nat.add_zero]
      have hmap := congrArg
        (fun q => q (cupCocycle (Rep.trivial ℤ G ℤ)
          (Rep.trivial ℤ G ℤ) n 0 xc integralUnitCocycle))
        (groupCohomology.π_map
          (f := MonoidHom.id G)
          (φ := (λ_ (Rep.trivial ℤ G ℤ)).hom) n)
      simp only [ConcreteCategory.comp_apply] at hmap
      calc
        _ = groupCohomology.π (Rep.trivial ℤ G ℤ) n
            (groupCohomology.cocyclesMap (MonoidHom.id G)
              (λ_ (Rep.trivial ℤ G ℤ)).hom n
              (cupCocycle (Rep.trivial ℤ G ℤ)
                (Rep.trivial ℤ G ℤ) n 0 xc integralUnitCocycle)) := hmap
        _ = groupCohomology.π (Rep.trivial ℤ G ℤ) n xc := by
          apply congrArg (groupCohomology.π (Rep.trivial ℤ G ℤ) n)
          apply (ModuleCat.mono_iff_injective
            (groupCohomology.iCocycles (Rep.trivial ℤ G ℤ) n)).1 inferInstance
          rw [i_cocycles_id]
          have hcup := i_cup_cocycle
            (Rep.trivial ℤ G ℤ) (Rep.trivial ℤ G ℤ) n 0
              xc integralUnitCocycle
          ext q
          have hcupq :
              groupCohomology.iCocycles
                  (𝟙_ (Rep ℤ G) ⊗ Rep.trivial ℤ G ℤ : Rep ℤ G) n
                  (cupCocycle (Rep.trivial ℤ G ℤ) (Rep.trivial ℤ G ℤ)
                    n 0 xc integralUnitCocycle) q =
                cochainCup (Rep.trivial ℤ G ℤ) (Rep.trivial ℤ G ℤ) n 0
                  (groupCohomology.iCocycles (Rep.trivial ℤ G ℤ) n xc)
                  (groupCohomology.iCocycles (Rep.trivial ℤ G ℤ) 0
                    integralUnitCocycle) q := by
            simpa only [Nat.add_zero] using congrFun hcup q
          have hone :
              groupCohomology.iCocycles (Rep.trivial ℤ G ℤ) 0
                  integralUnitCocycle =
                (fun _ : Fin 0 → G => (1 : ℤ)) := by
            rw [integralUnitCocycle]
            have h := groupCohomology.cocyclesIso₀_inv_comp_iCocycles_apply
              (Rep.trivial ℤ G ℤ) ⟨(1 : ℤ), by intro g; rfl⟩
            exact h.trans (by rfl)
          calc
            _ = (λ_ (Rep.trivial ℤ G ℤ)).hom
                (cochainCup (Rep.trivial ℤ G ℤ) (Rep.trivial ℤ G ℤ)
                  n 0
                  (groupCohomology.iCocycles (Rep.trivial ℤ G ℤ) n xc)
                  (groupCohomology.iCocycles (Rep.trivial ℤ G ℤ) 0
                    integralUnitCocycle) q) :=
              congrArg (λ_ (Rep.trivial ℤ G ℤ)).hom hcupq
            _ = _ := by
              rw [hone]
              simp [cochainCup, tensorElement,
                initialProduct]

/-- The two connecting maps in Tate's four-term sequence are cup product
with the chosen degree-two class.  This is the ordinary-cohomology range of
Remark II.3.13, including degree zero. -/
theorem double_boundary_cup
    (C : Rep ℤ G) (gamma : groupCohomology C 2) (n : ℕ)
    (a : groupCohomology (Rep.trivial ℤ G ℤ) n) :
    let φ := normalizedCocycleClass C gamma
    let hφ := normalized_cocycle_class C gamma
    groupCohomology.map (MonoidHom.id G) (λ_ C).hom (n + 2)
        (cupCohomology (Rep.trivial ℤ G ℤ) C n 2 a gamma) =
      groupCohomology.δ (splitting_sequence_short C φ hφ)
        (n + 1) (n + 2) rfl
        (groupCohomology.δ (augmentation_short_exact (G := G))
          n (n + 1) rfl a) := by
  dsimp only
  let φ := normalizedCocycleClass C gamma
  let hφ := normalized_cocycle_class C gamma
  let X := splittingModuleSequence C φ hφ
  let Y := augmentationSequence (G := G)
  let Z := Rep.trivial ℤ G ℤ
  let hX : X.ShortExact := splitting_sequence_short C φ hφ
  let hY : Y.ShortExact := augmentation_short_exact
  let hZX : (leftShortComplex Z X).ShortExact := by
    simpa [Z, X] using splitting_short_exact Z C φ hφ
  let hZY : (leftShortComplex Z Y).ShortExact := by
    simpa [Z, Y] using tensor_sequence_short (G := G) Z
  let u := integralUnit (G := G)
  let b := groupCohomology.δ hY 0 1 rfl u
  let s : ℤ := (-1 : ℤ) ^ n
  have hb : groupCohomology.δ hX 1 2 rfl b = gamma := by
    rw [show b = groupCohomology.H1π _ (augmentationCocycle (G := G)) by
      exact boundary_integral_unit]
    exact splitting_boundary_cocycle C gamma
  have houter := cup_cohomology_delta Z hX hZX n 1 a b
  have hinner := cup_cohomology_delta Z hY hZY n 0 a u
  have hinner' :
      cupCohomology Z X.X₃ n 1 a b =
        (-1 : ℤ) ^ n •
          groupCohomology.δ hZY n (n + 1) rfl
            (cupCohomology Z Y.X₃ n 0 a u) := by
    simpa [X, Y] using hinner
  have hunit := cup_integral_right n a
  have hnatY := unitor_delta_naturality Y hZY hY n
    (cupCohomology Z Y.X₃ n 0 a u)
  have hnatY' :
      groupCohomology.map (MonoidHom.id G) (λ_ X.X₃).hom (n + 1)
          (groupCohomology.δ hZY n (n + 1) rfl
            (cupCohomology Z Y.X₃ n 0 a u)) =
        groupCohomology.δ hY n (n + 1) rfl
          (groupCohomology.map (MonoidHom.id G) (λ_ Y.X₃).hom n
            (cupCohomology Z Y.X₃ n 0 a u)) := by
    simpa [X, Y] using hnatY
  have hnatX := unitor_delta_naturality X hZX hX (n + 1)
    (groupCohomology.δ hZY n (n + 1) rfl
      (cupCohomology Z Y.X₃ n 0 a u))
  rw [hb] at houter
  rw [hinner'] at houter
  change cupCohomology Z C n 2 a gamma =
      s • groupCohomology.δ hZX (n + 1) (n + 2) rfl
        (s • groupCohomology.δ hZY n (n + 1) rfl
          (cupCohomology Z Y.X₃ n 0 a u)) at houter
  have hsign :
      s • groupCohomology.δ hZX (n + 1) (n + 2) rfl
          (s • groupCohomology.δ hZY n (n + 1) rfl
            (cupCohomology Z Y.X₃ n 0 a u)) =
        groupCohomology.δ hZX (n + 1) (n + 2) rfl
          (groupCohomology.δ hZY n (n + 1) rfl
            (cupCohomology Z Y.X₃ n 0 a u)) := by
    let v := groupCohomology.δ hZY n (n + 1) rfl
      (cupCohomology Z Y.X₃ n 0 a u)
    have hδ : groupCohomology.δ hZX (n + 1) (n + 2) rfl (s • v) =
        s • groupCohomology.δ hZX (n + 1) (n + 2) rfl v :=
      map_zsmul (groupCohomology.δ hZX (n + 1) (n + 2) rfl).hom s v
    change s • groupCohomology.δ hZX (n + 1) (n + 2) rfl (s • v) = _
    rw [hδ, ← smul_assoc]
    have hs : s • s = (1 : ℤ) := by
      change s * s = 1
      simp [s, ← pow_add]
    rw [hs, one_smul]
  have houter' :
      cupCohomology Z C n 2 a gamma =
        groupCohomology.δ hZX (n + 1) (n + 2) rfl
          (groupCohomology.δ hZY n (n + 1) rfl
            (cupCohomology Z Y.X₃ n 0 a u)) := houter.trans hsign
  rw [houter']
  change
    groupCohomology.map (MonoidHom.id G) (λ_ X.X₁).hom ((n + 1) + 1)
        (groupCohomology.δ hZX (n + 1) ((n + 1) + 1) rfl
          (groupCohomology.δ hZY n (n + 1) rfl
            (cupCohomology Z Y.X₃ n 0 a u))) =
      groupCohomology.δ hX (n + 1) ((n + 1) + 1) rfl
        (groupCohomology.δ hY n (n + 1) rfl a)
  rw [hnatX, hnatY']
  have hunit' :
      groupCohomology.map (MonoidHom.id G) (λ_ Y.X₃).hom n
          (cupCohomology Z Y.X₃ n 0 a u) = a := by
    simpa [Z, Y, u] using hunit
  rw [hunit']

theorem cohomology_double_shift
    {X Y : ShortComplex (Rep ℤ G)}
    (hX : X.ShortExact) (hY : Y.ShortExact)
    (e : Y.X₁ ≅ X.X₃)
    (hXacyclic : ∀ m : ℕ, 0 < m →
      IsZero (groupCohomology X.X₂ m))
    (hYacyclic : ∀ m : ℕ, 0 < m →
      IsZero (groupCohomology Y.X₂ m))
    (n : ℕ) (hn : 0 < n) (a : groupCohomology Y.X₃ n) :
    (positiveDoubleShift hX hY e hXacyclic hYacyclic n hn).hom a =
      groupCohomology.δ hX (n + 1) ((n + 1) + 1) rfl
        (groupCohomology.map (MonoidHom.id G) e.hom (n + 1)
          (groupCohomology.δ hY n (n + 1) rfl a)) := by
  rfl

/-- In positive degree, the concrete double dimension-shifting isomorphism
used in Theorem II.3.11 is cup product with `gamma`. -/
theorem positive_double_shift
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hXacyclic : ∀ m : ℕ, 0 < m →
      IsZero (groupCohomology
        (splittingModuleClass C gamma) m))
    (hYacyclic : ∀ m : ℕ, 0 < m →
      IsZero (groupCohomology (Rep.leftRegular ℤ G) m))
    (n : ℕ) (hn : 0 < n)
    (a : groupCohomology (Rep.trivial ℤ G ℤ) n) :
    groupCohomology.map (MonoidHom.id G) (λ_ C).hom (n + 2)
        (cupCohomology (Rep.trivial ℤ G ℤ) C n 2 a gamma) =
      (positiveDoubleShift
        (splitting_sequence_short C
          (normalizedCocycleClass C gamma)
          (normalized_cocycle_class C gamma))
        (augmentation_short_exact (G := G)) (Iso.refl _)
        hXacyclic hYacyclic n hn).hom a := by
  let z := groupCohomology.δ (augmentation_short_exact (G := G))
    n (n + 1) rfl a
  have hid :
      groupCohomology.map (MonoidHom.id G)
          (Iso.refl (augmentationSequence (G := G)).X₁).hom (n + 1) z = z := by
    change groupCohomology.map (MonoidHom.id G)
      (𝟙 (augmentationIdealRep (G := G))) (n + 1) z = z
    have hmap := groupCohomology.map_id
      (G := G) (B := augmentationIdealRep (G := G)) (n := n + 1)
    simpa only [ConcreteCategory.id_apply] using congrArg (fun f ↦ f z) hmap
  have hshift := cohomology_double_shift
    (splitting_sequence_short C
      (normalizedCocycleClass C gamma)
      (normalized_cocycle_class C gamma))
    (augmentation_short_exact (G := G)) (Iso.refl _)
    hXacyclic hYacyclic n hn a
  have hshift' :
      (positiveDoubleShift
        (splitting_sequence_short C
          (normalizedCocycleClass C gamma)
          (normalized_cocycle_class C gamma))
        (augmentation_short_exact (G := G)) (Iso.refl _)
        hXacyclic hYacyclic n hn).hom a =
      groupCohomology.δ
        (splitting_sequence_short C
          (normalizedCocycleClass C gamma)
          (normalized_cocycle_class C gamma))
        (n + 1) ((n + 1) + 1) rfl z := by
    calc
      _ = groupCohomology.δ
          (splitting_sequence_short C
            (normalizedCocycleClass C gamma)
            (normalized_cocycle_class C gamma))
          (n + 1) ((n + 1) + 1) rfl
          (groupCohomology.map (MonoidHom.id G)
            (Iso.refl (augmentationSequence (G := G)).X₁).hom (n + 1) z) := by
              simpa [z] using hshift
      _ = _ := congrArg
        (groupCohomology.δ
          (splitting_sequence_short C
            (normalizedCocycleClass C gamma)
            (normalized_cocycle_class C gamma))
          (n + 1) ((n + 1) + 1) rfl) hid
  have hcore := double_boundary_cup C gamma n a
  simpa [z] using hcore.trans hshift'.symm

end

end Towers.CField.Shifting
