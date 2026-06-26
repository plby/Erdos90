import Towers.ClassField.Shifting.CupProduct
import Towers.ClassField.Shifting.AssemblingTensorShift
import Towers.ClassField.Shifting.NormExactSequence

/-!
# Milne, Class Field Theory, Proposition II.3.4 and Remark II.3.5

Let `G` be a finite cyclic group with chosen generator `g`.  The first four
terms of the standard cyclic resolution are

`0 ⟶ ℤ ⟶ ℤ[G] ⟶ I_G ⟶ 0`,

followed by the augmentation sequence

`0 ⟶ I_G ⟶ ℤ[G] ⟶ ℤ ⟶ 0`.

The first map sends an integer to that multiple of the norm element and the
second map is `g - 1`.  Tensoring both sequences with an arbitrary
`G`-representation gives Milne's four-term sequence

`0 ⟶ M ⟶ ℤ[G] ⊗ M ⟶ ℤ[G] ⊗ M ⟶ M ⟶ 0`.

Both middle terms are Tate-acyclic.  The two connecting maps therefore give
the unconditional two-periodicity isomorphism in every Tate range represented
in the project.  The degree-two class obtained from the same two boundaries
is the cyclic period class; compatibility of cup products with connecting
maps identifies the positive-degree period map with cup product by this
class.  Degree zero is recorded on invariant representatives as well.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits MonoidalCategory Rep Representation
open scoped MonoidalCategory TensorProduct
open Towers.CField.COps.CPBuild
open Towers.CField.TCohomo

noncomputable section

variable {G : Type} [CommGroup G] [Fintype G]

omit [Fintype G] in
private theorem unitor_tensor_int
    (A : Rep ℤ G) (a : A) (z : ℤ) :
    (ρ_ A).hom
        (tensorElement A (𝟙_ (Rep ℤ G)) a z) = z • a := by
  simp only [tensor_V, tensorUnit_V, tensor_ρ, tensorUnit_ρ,
    hom_hom_rightUnitor,
    Representation.Equiv.coe_toIntertwiningMap]
  exact int_smul_eq_zsmul A.hV2 z a

private theorem tate_iso_projection
    {k K : Type} [CommRing k] [Group K] [Fintype K]
    {A B : Rep k K} (e : A ≅ B) (z : A.ρ.invariants) :
    tateZeroIso e
        (tateCohomologyProjection A z) =
      tateCohomologyProjection B
        (((Rep.invariantsFunctor k K).map e.hom).hom z) := by
  rfl

/-- The norm element of the integral group ring, with coefficient `z`. -/
noncomputable def cyclicNormElement (z : ℤ) : IntegralGroupRing G :=
  Finsupp.equivFunOnFinite.symm (fun _ : G ↦ z)

omit [CommGroup G] in
@[simp]
theorem cyclic_norm_element (z : ℤ) (h : G) :
    cyclicNormElement (G := G) z h = z := by
  rfl

theorem cyclic_element_invariant (z : ℤ) (g : G) :
    (Rep.leftRegular ℤ G).ρ g (cyclicNormElement (G := G) z) =
      cyclicNormElement (G := G) z := by
  ext h
  rw [Representation.ofMulAction_apply, cyclic_norm_element,
    cyclic_norm_element]

/-- The inclusion `ℤ ⟶ ℤ[G]` that sends `1` to the norm element. -/
noncomputable def cyclicNormInclusion :
    Rep.trivial ℤ G ℤ ⟶ Rep.leftRegular ℤ G :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := cyclicNormElement (G := G)
          map_add' := by
            intro x y
            ext h
            simp
          map_smul' := by
            intro x y
            ext h
            simp }
      isIntertwining' := fun g ↦ by
        apply LinearMap.ext
        intro z
        change cyclicNormElement (G := G) z =
          (Rep.leftRegular ℤ G).ρ g (cyclicNormElement (G := G) z)
        exact (cyclic_element_invariant z g).symm }

@[simp]
theorem cyclic_norm_inclusion (z : ℤ) :
    cyclicNormInclusion (G := G) z = cyclicNormElement (G := G) z :=
  rfl

/-- Right multiplication by `g - 1`, with codomain restricted to the
augmentation ideal.  Commutativity of `G` makes this a morphism for the left
regular action. -/
noncomputable def cyclicDifferenceIdeal (g : G) :
    Rep.leftRegular ℤ G ⟶ augmentationIdealRep (G := G) :=
  Rep.ofHom
    { toLinearMap :=
        { toFun := fun x ↦
            ⟨(Rep.applyAsHom (Rep.leftRegular ℤ G) g -
                𝟙 (Rep.leftRegular ℤ G)).hom x,
              by
                calc
                  augmentation G ((Rep.leftRegular ℤ G).ρ g x - x) =
                      augmentation G ((Rep.leftRegular ℤ G).ρ g x) -
                        augmentation G x := map_sub _ _ _
                  _ = 0 := by
                    rw [augmentation_regular_action]
                    simp⟩
          map_add' := by
            intro x y
            apply Subtype.ext
            exact map_add _ x y
          map_smul' := by
            intro z x
            apply Subtype.ext
            exact ((Rep.applyAsHom (Rep.leftRegular ℤ G) g -
              𝟙 (Rep.leftRegular ℤ G)).hom.toLinearMap).map_smul z x }
      isIntertwining' := fun h ↦ by
        apply LinearMap.ext
        intro x
        let D : Rep.leftRegular ℤ G ⟶ Rep.leftRegular ℤ G :=
          Rep.applyAsHom (Rep.leftRegular ℤ G) g - 𝟙 (Rep.leftRegular ℤ G)
        change
          (⟨D.hom ((Rep.leftRegular ℤ G).ρ h x), _⟩ : augmentationIdeal G) =
            augmentationLeftAction h
              ⟨D.hom x, _⟩
        apply Subtype.ext
        rw [augmentation_action_coe]
        calc
          (show IntegralGroupRing G from
              (⟨D.hom ((Rep.leftRegular ℤ G).ρ h x), _⟩ :
                augmentationIdeal G).1) =
              (show IntegralGroupRing G from
                D.hom ((Rep.leftRegular ℤ G).ρ h x)) := rfl
          _ = (show IntegralGroupRing G from
                (Rep.leftRegular ℤ G).ρ h (D.hom x)) :=
            Rep.hom_comm_apply D h x
          _ = MonoidAlgebra.single h (1 : ℤ) *
              (show IntegralGroupRing G from D.hom x) :=
            regular_int_action h _
          _ = MonoidAlgebra.single h (1 : ℤ) *
              (⟨D.hom x, _⟩ : augmentationIdeal G).1 := rfl }

omit [Fintype G] in
@[simp]
theorem cyclic_difference_coe (g : G)
    (x : IntegralGroupRing G) :
    (cyclicDifferenceIdeal g x).1 =
      (Rep.applyAsHom (Rep.leftRegular ℤ G) g -
        𝟙 (Rep.leftRegular ℤ G)).hom x :=
  rfl

/-- The first short exact sequence in the four-term cyclic resolution. -/
noncomputable def cyclicDifferenceSequence (g : G) :
    ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (cyclicNormInclusion (G := G))
    (cyclicDifferenceIdeal g) <| by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      change (cyclicDifferenceIdeal g
        (cyclicNormElement (G := G) z)).1 = 0
      rw [cyclic_difference_coe]
      dsimp only [Rep.sub_hom, Rep.applyAsHom]
      exact sub_eq_zero.mpr (cyclic_element_invariant (G := G) z g)

private theorem cyclic_inclusion_injective :
    Function.Injective (cyclicNormInclusion (G := G)) := by
  intro x y hxy
  have h := congrArg (fun q : IntegralGroupRing G ↦ q 1) hxy
  change cyclicNormElement (G := G) x 1 =
    cyclicNormElement (G := G) y 1 at h
  simpa only [cyclic_norm_element] using h

omit [Fintype G] in
private theorem augmentation_linear_combination (x : IntegralGroupRing G) :
    augmentation G x = Finsupp.linearCombination ℤ (fun _ : G ↦ (1 : ℤ)) x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
      calc
        augmentation G (x + y) = augmentation G x + augmentation G y := map_add _ _ _
        _ = Finsupp.linearCombination ℤ (fun _ : G ↦ (1 : ℤ)) x +
            Finsupp.linearCombination ℤ (fun _ : G ↦ (1 : ℤ)) y := by rw [hx, hy]
        _ = Finsupp.linearCombination ℤ (fun _ : G ↦ (1 : ℤ)) (x + y) :=
          (map_add _ _ _).symm
  | single h z => simp

omit [Fintype G] in
private theorem cyclic_difference_surjective [Finite G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Function.Surjective (cyclicDifferenceIdeal g) := by
  letI : Fintype G := Fintype.ofFinite G
  intro y
  have hy : (y.1 : IntegralGroupRing G) ∈
      LinearMap.ker (Finsupp.linearCombination ℤ (fun _ : G ↦ (1 : ℤ))) := by
    change Finsupp.linearCombination ℤ (fun _ : G ↦ (1 : ℤ)) y.1 = 0
    calc
      Finsupp.linearCombination ℤ (fun _ : G ↦ (1 : ℤ)) y.1 =
          augmentation G y.1 := (augmentation_linear_combination y.1).symm
      _ = 0 := y.2
  rw [← Rep.FiniteCyclicGroup.leftRegular.range_applyAsHom_sub_eq_ker_linearCombination
      ℤ g hg] at hy
  obtain ⟨x, hx⟩ := hy
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

private theorem cyclic_element_regular (x : IntegralGroupRing G) :
    cyclicNormElement (G := G) (augmentation G x) =
      (Rep.leftRegular ℤ G).norm.hom x := by
  change cyclicNormElement (G := G) (augmentation G x) =
    (Rep.leftRegular ℤ G).ρ.norm x
  rw [Representation.leftRegular_norm_apply]
  change cyclicNormElement (G := G) (augmentation G x) =
    (Finsupp.linearCombination ℤ (fun _ : G ↦ (1 : ℤ)) x) •
      (Rep.leftRegular ℤ G).ρ.norm
      (MonoidAlgebra.single 1 1)
  rw [← augmentation_linear_combination]
  ext h
  rw [cyclic_norm_element]
  simp [Representation.norm]

/-- The norm/difference sequence is short exact when `g` generates `G`. -/
theorem difference_short_exact
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    (cyclicDifferenceSequence g).ShortExact := by
  letI repModule (A : Rep.{0} ℤ G) : Module ℤ A := A.hV2
  let F : Functor (Rep.{0} ℤ G) (ModuleCat.{0} ℤ) :=
    forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ)
  let X : ShortComplex (Rep.{0} ℤ G) := cyclicDifferenceSequence g
  let S : ShortComplex (ModuleCat.{0} ℤ) := X.map F
  have hS : S.Exact := (ShortComplex.moduleCat_exact_iff S).2 fun x hx ↦ by
    have hx0 : (Rep.applyAsHom (Rep.leftRegular ℤ G) g -
        𝟙 (Rep.leftRegular ℤ G)).hom.toLinearMap x = 0 :=
      congrArg Subtype.val hx
    have hxmem : x ∈ LinearMap.ker
        (Rep.applyAsHom (Rep.leftRegular ℤ G) g -
          𝟙 (Rep.leftRegular ℤ G)).hom.toLinearMap := hx0
    rw [← Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub
        ℤ g hg] at hxmem
    obtain ⟨y, hy⟩ := hxmem
    refine ⟨augmentation G y, ?_⟩
    change cyclicNormElement (G := G) (augmentation G y) = x
    rw [cyclic_element_regular]
    exact hy
  exact
    { exact := F.reflects_exact_of_faithful X hS
      mono_f := (Rep.mono_iff_injective _).2 cyclic_inclusion_injective
      epi_g := (Rep.epi_iff_surjective _).2
        (cyclic_difference_surjective g hg) }

/-- Evaluation at `1` retracts the norm inclusion after forgetting the
group action. -/
noncomputable def cyclicInclusionRetraction :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ)
      (Rep.leftRegular ℤ G) (Rep.trivial ℤ G ℤ) _ _
      (Rep.leftRegular ℤ G).hV2 (Rep.trivial ℤ G ℤ).hV2 :=
  { toFun := fun x ↦ x 1
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

theorem cyclic_inclusion_retraction :
    Function.LeftInverse (cyclicInclusionRetraction (G := G))
      (cyclicNormInclusion (G := G)) := by
  intro z
  change cyclicNormElement (G := G) z 1 = z
  exact cyclic_norm_element z 1

/-- Tensoring the first cyclic short exact sequence with arbitrary
coefficients preserves short exactness. -/
theorem tensor_short_exact
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    ((cyclicDifferenceSequence g).map
      ((tensoringLeft (Rep ℤ G)).obj A)).ShortExact := by
  apply tensor_short_retraction A
    (difference_short_exact g hg)
    cyclicInclusionRetraction
    cyclic_inclusion_retraction

/-- The degree-two class defined by the first four terms of the cyclic
resolution.  This is the period class attached to the chosen generator. -/
noncomputable def cyclicPeriodicityClass (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    groupCohomology (Rep.trivial ℤ G ℤ) 2 :=
  groupCohomology.δ (difference_short_exact g hg)
      1 2 rfl
    (groupCohomology.δ (augmentation_short_exact (G := G))
      0 1 rfl integralUnit)

/-- The all-range cyclic period shift, before removing the tensor unit at
its source and target. -/
noncomputable def cyclicShiftTensor
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    TSCoeffi
      (A ⊗ Rep.trivial ℤ G ℤ) (A ⊗ Rep.trivial ℤ G ℤ) := by
  let X := (cyclicDifferenceSequence g).map
    ((tensoringLeft (Rep ℤ G)).obj A)
  let Y := (augmentationSequence (G := G)).map
    ((tensoringLeft (Rep ℤ G)).obj A)
  have hX : X.ShortExact := tensor_short_exact A g hg
  have hY : Y.ShortExact := tensor_sequence_short A
  have hXAcyclic : TateAcyclic X.X₂ := by
    simpa [X, cyclicDifferenceSequence] using tensor_regular_acyclic A
  have hYAcyclic : TateAcyclic Y.X₂ := by
    simpa [Y, augmentationSequence] using tensor_regular_acyclic A
  let e : Y.X₁ ≅ X.X₃ := Iso.refl _
  simpa [X, Y, cyclicDifferenceSequence, augmentationSequence] using
    shiftSplicedShort hX hY e hXAcyclic hYAcyclic

/-- Transport the target of an all-range Tate shift across an isomorphism
of representations. -/
noncomputable def TSCoeffi.transTarget
    {A C C' : Rep ℤ G} (s : TSCoeffi A C)
    (e : C ≅ C') : TSCoeffi A C' :=
  { positive := fun n hn ↦
      (s.positive n hn).trans
        ((groupCohomology.functor ℤ G (n + 2)).mapIso e).toLinearEquiv.toAddEquiv
    zero := s.zero.trans
      ((groupCohomology.functor ℤ G 2).mapIso e).toLinearEquiv.toAddEquiv
    negOne := s.negOne.trans
      ((groupCohomology.functor ℤ G 1).mapIso e).toLinearEquiv.toAddEquiv
    negTwo := s.negTwo.trans (tateAddIso e)
    negThree := s.negThree.trans (tateCohomologyIso e)
    lower := fun n hn ↦
      (s.lower n hn).trans
        ((groupHomology.functor ℤ G n).mapIso e).toLinearEquiv.toAddEquiv }

/-- **Proposition II.3.4 (all Tate degrees).**  A chosen generator of a
finite cyclic group determines unconditional isomorphisms
`H_T^r(G,A) ≃ H_T^(r+2)(G,A)` for every coefficient module `A`.

The project represents the integer-graded Tate theory in six ranges; this
single value contains all six isomorphisms.  Its construction is exactly the
tensorized four-term sequence in the proof in `CFT.tex`. -/
noncomputable def cyclicTateShift
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    TSCoeffi A A :=
  ((cyclicShiftTensor A g hg).transSource (ρ_ A).symm).transTarget
    (ρ_ A)

/-- Cup product with the period class is the composite of the two
connecting maps after tensoring the cyclic four-term sequence.  This is the
cohomological calculation in Remark II.3.5, before removing the right tensor
unit. -/
theorem periodicity_double_boundary
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (n : ℕ) (a : groupCohomology A n) :
    cupCohomology A (Rep.trivial ℤ G ℤ) n 2 a
        (cyclicPeriodicityClass g hg) =
      groupCohomology.δ
        (tensor_short_exact A g hg)
        (n + 1) (n + 2) (by omega)
        (groupCohomology.δ (tensor_sequence_short A)
          n (n + 1) rfl
          (cupCohomology A (Rep.trivial ℤ G ℤ) n 0 a integralUnit)) := by
  let X := cyclicDifferenceSequence g
  let Y := augmentationSequence (G := G)
  let Z := Rep.trivial ℤ G ℤ
  let hX : X.ShortExact := difference_short_exact g hg
  let hY : Y.ShortExact := augmentation_short_exact
  let hAX : (leftShortComplex A X).ShortExact :=
    tensor_short_exact A g hg
  let hAY : (leftShortComplex A Y).ShortExact :=
    tensor_sequence_short A
  let u := integralUnit (G := G)
  let b := groupCohomology.δ hY 0 1 rfl u
  let s : ℤ := (-1 : ℤ) ^ n
  have houter := cup_cohomology_delta A hX hAX n 1 a b
  have hinner := cup_cohomology_delta A hY hAY n 0 a u
  have hinner' :
      cupCohomology A X.X₃ n 1 a b =
        s • groupCohomology.δ hAY n (n + 1) rfl
          (cupCohomology A Y.X₃ n 0 a u) := by
    simpa [X, Y, b, u, s] using hinner
  change cupCohomology A Z n 2 a
      (groupCohomology.δ hX 1 2 rfl b) = _
  change cupCohomology A X.X₁ n (1 + 1) a
      (groupCohomology.δ hX 1 (1 + 1) rfl b) = _
  rw [houter]
  change s • groupCohomology.δ hAX (n + 1) ((n + 1) + 1) rfl
      (cupCohomology A X.X₃ n 1 a b) = _
  rw [hinner']
  let v := groupCohomology.δ hAY n (n + 1) rfl
    (cupCohomology A Y.X₃ n 0 a u)
  rw [show groupCohomology.δ hAX (n + 1) ((n + 1) + 1) rfl
      (s • v) = s • groupCohomology.δ hAX (n + 1) ((n + 1) + 1) rfl v by
    exact map_zsmul
      (groupCohomology.δ hAX (n + 1) ((n + 1) + 1) rfl).hom s v]
  rw [← smul_assoc]
  have hs : s • s = (1 : ℤ) := by
    change s * s = 1
    dsimp [s]
    rw [← pow_add]
    have hadd : n + n = 2 * n := by omega
    rw [hadd, pow_mul]
    norm_num
  rw [hs, one_smul]
  dsimp [v]
  rfl

omit [Fintype G] in
theorem cup_integral_general
    (A : Rep ℤ G) (n : ℕ) (x : groupCohomology A n) :
    groupCohomology.map (MonoidHom.id G) (ρ_ A).hom n
        (cupCohomology A (Rep.trivial ℤ G ℤ) n 0 x integralUnit) = x := by
  induction x using groupCohomology_induction_on with
  | h xc =>
      rw [integralUnit, cupCohomology_π]
      simp only [Nat.add_zero]
      have hmap := congrArg
        (fun q => q (cupCocycle A (Rep.trivial ℤ G ℤ) n 0 xc integralUnitCocycle))
        (groupCohomology.π_map
          (f := MonoidHom.id G) (φ := (ρ_ A).hom) n)
      simp only [ConcreteCategory.comp_apply] at hmap
      calc
        _ = groupCohomology.π A n
            (groupCohomology.cocyclesMap (MonoidHom.id G) (ρ_ A).hom n
              (cupCocycle A (Rep.trivial ℤ G ℤ) n 0 xc integralUnitCocycle)) := hmap
        _ = groupCohomology.π A n xc := by
          apply congrArg (groupCohomology.π A n)
          apply (ModuleCat.mono_iff_injective
            (groupCohomology.iCocycles A n)).1 inferInstance
          rw [i_cocycles_id]
          have hcup := i_cup_cocycle A (Rep.trivial ℤ G ℤ) n 0
            xc integralUnitCocycle
          ext q
          have hcupq :
              groupCohomology.iCocycles
                  (A ⊗ Rep.trivial ℤ G ℤ : Rep ℤ G) n
                  (cupCocycle A (Rep.trivial ℤ G ℤ) n 0
                    xc integralUnitCocycle) q =
                cochainCup A (Rep.trivial ℤ G ℤ) n 0
                  (groupCohomology.iCocycles A n xc)
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
            _ = (ρ_ A).hom
                (cochainCup A (Rep.trivial ℤ G ℤ) n 0
                  (groupCohomology.iCocycles A n xc)
                  (groupCohomology.iCocycles (Rep.trivial ℤ G ℤ) 0
                    integralUnitCocycle) q) :=
              congrArg (ρ_ A).hom hcupq
            _ = _ := by
              rw [hone]
              change (ρ_ A).hom
                (tensorElement A (𝟙_ (Rep ℤ G))
                  (groupCohomology.iCocycles A n xc q) (1 : ℤ)) =
                groupCohomology.iCocycles A n xc q
              rw [unitor_tensor_int, one_zsmul]

omit [Fintype G] in
/-- Mapping a class into `A ⊗ ℤ` through the inverse right unitor is the
same as cupping it with the integral unit in degree zero. -/
theorem unitor_inv_cup
    (A : Rep ℤ G) (n : ℕ) (a : groupCohomology A n) :
    groupCohomology.map (MonoidHom.id G) (ρ_ A).inv n a =
      cupCohomology A (Rep.trivial ℤ G ℤ) n 0 a integralUnit := by
  let e := (groupCohomology.functor ℤ G n).mapIso (ρ_ A)
  change e.inv a = _
  apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
  rw [e.inv_hom_id_apply]
  simpa [e] using (cup_integral_general A n a).symm

/-- The ordinary positive-degree period equivalence obtained directly from
the tensorized four-term cyclic sequence. -/
noncomputable def cyclicCupPeriodicity
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : 0 < n) :
    groupCohomology A n ≃+ groupCohomology A (n + 2) := by
  let X := (cyclicDifferenceSequence g).map
    ((tensoringLeft (Rep ℤ G)).obj A)
  let Y := (augmentationSequence (G := G)).map
    ((tensoringLeft (Rep ℤ G)).obj A)
  let hX : X.ShortExact := tensor_short_exact A g hg
  let hY : Y.ShortExact := tensor_sequence_short A
  let hXAcyclic : ∀ m : ℕ, 0 < m → IsZero (groupCohomology X.X₂ m) := by
    intro m hm
    simpa [X, cyclicDifferenceSequence] using
      (tensor_regular_acyclic A).positiveCohomology m hm
  let hYAcyclic : ∀ m : ℕ, 0 < m → IsZero (groupCohomology Y.X₂ m) := by
    intro m hm
    simpa [Y, augmentationSequence] using
      (tensor_regular_acyclic A).positiveCohomology m hm
  let e : Y.X₁ ≅ X.X₃ := Iso.refl _
  let source : groupCohomology A n ≃+
      groupCohomology Y.X₃ n := by
    simpa [Y, augmentationSequence] using
      ((groupCohomology.functor ℤ G n).mapIso (ρ_ A).symm).toLinearEquiv.toAddEquiv
  let middle :=
    (positiveDoubleShift hX hY e hXAcyclic hYAcyclic n hn).toLinearEquiv.toAddEquiv
  let target : groupCohomology X.X₁ (n + 2) ≃+
      groupCohomology A (n + 2) := by
    simpa [X, cyclicDifferenceSequence] using
      ((groupCohomology.functor ℤ G (n + 2)).mapIso (ρ_ A)).toLinearEquiv.toAddEquiv
  exact source.trans middle |>.trans target

/-- **Remark II.3.5, ordinary positive degrees.**  The positive-degree
cyclic period isomorphism is literal cup product with the period class
attached to the chosen generator. -/
theorem cyclic_cup_periodicity
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (n : ℕ) (hn : 0 < n) (a : groupCohomology A n) :
    cyclicCupPeriodicity A g hg n hn a =
      groupCohomology.map (MonoidHom.id G) (ρ_ A).hom (n + 2)
        (cupCohomology A (Rep.trivial ℤ G ℤ) n 2 a
          (cyclicPeriodicityClass g hg)) := by
  let X := (cyclicDifferenceSequence g).map
    ((tensoringLeft (Rep ℤ G)).obj A)
  let Y := (augmentationSequence (G := G)).map
    ((tensoringLeft (Rep ℤ G)).obj A)
  let hX : X.ShortExact := tensor_short_exact A g hg
  let hY : Y.ShortExact := tensor_sequence_short A
  let hXAcyclic : ∀ m : ℕ, 0 < m → IsZero (groupCohomology X.X₂ m) := by
    intro m hm
    simpa [X, cyclicDifferenceSequence] using
      (tensor_regular_acyclic A).positiveCohomology m hm
  let hYAcyclic : ∀ m : ℕ, 0 < m → IsZero (groupCohomology Y.X₂ m) := by
    intro m hm
    simpa [Y, augmentationSequence] using
      (tensor_regular_acyclic A).positiveCohomology m hm
  let e : Y.X₁ ≅ X.X₃ := Iso.refl _
  let source : groupCohomology A n ≃+
      groupCohomology Y.X₃ n := by
    simpa [Y, augmentationSequence] using
      ((groupCohomology.functor ℤ G n).mapIso (ρ_ A).symm).toLinearEquiv.toAddEquiv
  let middle :=
    (positiveDoubleShift hX hY e hXAcyclic hYAcyclic n hn).toLinearEquiv.toAddEquiv
  let target : groupCohomology X.X₁ (n + 2) ≃+
      groupCohomology A (n + 2) := by
    simpa [X, cyclicDifferenceSequence] using
      ((groupCohomology.functor ℤ G (n + 2)).mapIso (ρ_ A)).toLinearEquiv.toAddEquiv
  change target (middle (source a)) = _
  have hsource : source a =
      cupCohomology A (Rep.trivial ℤ G ℤ) n 0 a integralUnit := by
    simpa [source, Y, augmentationSequence] using
      unitor_inv_cup A n a
  have hmiddle := cohomology_double_shift
    hX hY e hXAcyclic hYAcyclic n hn (source a)
  change middle (source a) = _ at hmiddle
  rw [hsource] at hmiddle
  rw [hsource, hmiddle]
  let z := groupCohomology.δ hY n (n + 1) rfl
    (cupCohomology A (Rep.trivial ℤ G ℤ) n 0 a integralUnit)
  have hemap : groupCohomology.map (MonoidHom.id G) e.hom (n + 1) z = z := by
    change groupCohomology.map (MonoidHom.id G) (𝟙 X.X₃) (n + 1) z = z
    have hmap := groupCohomology.map_id
      (G := G) (B := X.X₃) (n := n + 1)
    simpa only [ConcreteCategory.id_apply] using congrArg (fun f => f z) hmap
  rw [hemap]
  change target
      (groupCohomology.δ hX (n + 1) ((n + 1) + 1) rfl
        (groupCohomology.δ hY n (n + 1) rfl
          (cupCohomology A (Rep.trivial ℤ G ℤ) n 0 a integralUnit))) = _
  rw [← periodicity_double_boundary A g hg n a]
  rfl

/-- **Remark II.3.5, Tate degree zero.**  On an invariant representative,
the degree-zero component of cyclic Tate periodicity is cup product with the
period class. -/
theorem cyclic_shift_projection
    (A : Rep ℤ G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : groupCohomology A 0) :
    (cyclicTateShift A g hg).zero
        (tateCohomologyProjection A
          ((groupCohomology.H0Iso A).hom a)) =
      groupCohomology.map (MonoidHom.id G) (ρ_ A).hom 2
        (cupCohomology A (Rep.trivial ℤ G ℤ) 0 2 a
          (cyclicPeriodicityClass g hg)) := by
  let X := (cyclicDifferenceSequence g).map
    ((tensoringLeft (Rep ℤ G)).obj A)
  let Y := (augmentationSequence (G := G)).map
    ((tensoringLeft (Rep ℤ G)).obj A)
  let hX : X.ShortExact := tensor_short_exact A g hg
  let hY : Y.ShortExact := tensor_sequence_short A
  let hXAcyclic : TateAcyclic X.X₂ := by
    simpa [X, cyclicDifferenceSequence] using
      tensor_regular_acyclic A
  let hYAcyclic : TateAcyclic Y.X₂ := by
    simpa [Y, augmentationSequence] using tensor_regular_acyclic A
  let e : Y.X₁ ≅ X.X₃ := Iso.refl _
  let a' := groupCohomology.map (MonoidHom.id G) (ρ_ A).inv 0 a
  have hsource :
      tateAddIso (ρ_ A).symm
          (tateCohomologyProjection A
            ((groupCohomology.H0Iso A).hom a)) =
        tateCohomologyProjection Y.X₃
          ((groupCohomology.H0Iso Y.X₃).hom a') := by
    change tateZeroIso (ρ_ A).symm
      (tateCohomologyProjection A
        ((groupCohomology.H0Iso A).hom a)) = _
    rw [tate_iso_projection]
    apply congrArg (tateCohomologyProjection Y.X₃)
    have hnat := groupCohomology.map_id_comp_H0Iso_hom_apply
      (ρ_ A).inv a
    simpa [Y, augmentationSequence, a'] using hnat.symm
  have hshift := shift_spliced_short
    hX hY e hXAcyclic hYAcyclic
      ((groupCohomology.H0Iso Y.X₃).hom a')
  simp only [Iso.hom_inv_id_apply] at hshift
  have hemap :
      groupCohomology.map (MonoidHom.id G) e.hom 1
          (groupCohomology.δ hY 0 1 rfl a') =
        groupCohomology.δ hY 0 1 rfl a' := by
    change groupCohomology.map (MonoidHom.id G) (𝟙 X.X₃) 1
      (groupCohomology.δ hY 0 1 rfl a') = _
    have hmap := groupCohomology.map_id
      (G := G) (B := X.X₃) (n := 1)
    simpa only [ConcreteCategory.id_apply] using
      congrArg (fun f => f (groupCohomology.δ hY 0 1 rfl a')) hmap
  rw [hemap] at hshift
  change groupCohomology.map (MonoidHom.id G) (ρ_ A).hom 2
    ((cyclicShiftTensor A g hg).zero
      (tateAddIso (ρ_ A).symm
        (tateCohomologyProjection A
          ((groupCohomology.H0Iso A).hom a)))) = _
  rw [hsource]
  have hshift' :
      (cyclicShiftTensor A g hg).zero
          (tateCohomologyProjection Y.X₃
            ((groupCohomology.H0Iso Y.X₃).hom a')) =
        groupCohomology.δ hX 1 2 rfl
          (groupCohomology.δ hY 0 1 rfl a') := by
    simpa [cyclicShiftTensor, X, Y, e,
      cyclicDifferenceSequence, augmentationSequence] using hshift
  rw [hshift']
  have ha' : a' =
      cupCohomology A (Rep.trivial ℤ G ℤ) 0 0 a integralUnit := by
    simpa [a'] using unitor_inv_cup A 0 a
  rw [ha']
  rw [← periodicity_double_boundary A g hg 0 a]

end

end Towers.CField.Shifting
