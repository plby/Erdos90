import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.RepresentationTheory.FiniteIndex
import Towers.ClassField.Homological.EnoughInjectives
import Towers.ClassField.CohomologyOps.InflationRestrictionOne
import Towers.ClassField.CohomologyOps.InjectiveModuleVanishing

/-!
# Inflation across a cohomologically acyclic normal subgroup

This file supplies the dimension-shifting form of Proposition II.1.34 used
in the proof of Theorem II.3.10.
-/

namespace Towers.CField.COps

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Adjunction

variable (H : Subgroup G) [H.Normal]

instance functor_preserves_morphisms :
    (Rep.quotientToInvariantsFunctor.{u} k H).PreservesZeroMorphisms where
  map_zero _ _ := by ext; rfl

instance invariants_functor_additive :
    (Rep.quotientToInvariantsFunctor.{u} k H).Additive where
  map_add := by
    intro X Y f g
    ext
    rfl

/-- Inflation from `G/H` is left adjoint to taking `H`-invariants. -/
noncomputable def inflationInvariantsAdjunction :
    Rep.resFunctor.{u} (QuotientGroup.mk' H) ⊣
      Rep.quotientToInvariantsFunctor.{u} k H :=
  Adjunction.mkOfHomEquiv {
    homEquiv B A :=
      { toFun := fun f => Rep.ofHom ⟨
          f.hom.toLinearMap.codRestrict _ (fun b h => by
            change A.ρ h (f.hom b) = f.hom b
            rw [← hom_comm_apply f h b]
            change f.hom ((B.ρ (QuotientGroup.mk' H h)) b) = f.hom b
            have hh : QuotientGroup.mk' H h.1 = 1 :=
              (QuotientGroup.eq_one_iff h.1).2 h.2
            rw [hh]
            simp),
          fun q => by
            induction q using QuotientGroup.induction_on with
            | H g =>
                ext b
                exact hom_comm_apply f g b⟩
        invFun := fun f =>
          (Rep.resFunctor (QuotientGroup.mk' H)).map f ≫
            Rep.ofHom (A.ρ.quotientToInvariants_lift H)
        left_inv := fun f => by ext; rfl
        right_inv := fun f => by ext; rfl }
    homEquiv_naturality_left_symm := by
      intro B B' A f g
      ext
      rfl
    homEquiv_naturality_right := by
      intro B A A' f g
      ext
      rfl }

/-- Taking normal-subgroup invariants preserves injective representations,
because it is right adjoint to the exact inflation functor. -/
theorem quotient_invariants_injective (A : Rep.{u} k G) [Injective A] :
    Injective ((Rep.quotientToInvariantsFunctor.{u} k H).obj A) := by
  apply (inflationInvariantsAdjunction (k := k) H).map_injective
  infer_instance

set_option maxHeartbeats 2000000 in
-- Mapping the restricted short exact sequence is unusually expensive to elaborate.
/-- Taking `H`-invariants preserves a short exact sequence when the first
coefficient has vanishing `H^1`.  Left exactness comes from the adjunction;
surjectivity on the right is the degree-zero/degree-one part of the long
exact cohomology sequence. -/
theorem invariants_short_exact
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (h1 : IsZero (groupCohomology (Rep.res H.subtype X.X₁) 1)) :
    (X.map (Rep.quotientToInvariantsFunctor.{u} k H)).ShortExact := by
  let F := Rep.quotientToInvariantsFunctor.{u} k H
  change (X.map F).ShortExact
  letI : F.IsRightAdjoint :=
    (inflationInvariantsAdjunction (k := k) H).isRightAdjoint
  let Y := X.map (Rep.resFunctor H.subtype)
  have hres : Y.ShortExact :=
    hX.map_of_exact (Rep.resFunctor H.subtype)
  have h1Y : IsZero (groupCohomology Y.X₁ 1) := h1
  have hdelta : groupCohomology.δ hres 0 1 rfl = 0 :=
    h1Y.eq_of_tgt _ _
  haveI hmap0 : Epi
      (groupCohomology.mapShortComplex₃ (i := 0) (j := 1) hres rfl).f :=
    (groupCohomology.mapShortComplex₃_exact (i := 0) (j := 1) hres rfl).epi_f hdelta
  let q :=
    (groupCohomology.mapShortComplex₃ (i := 0) (j := 1) hres rfl).f
  haveI hq : Epi q := hmap0
  have hnat : q ≫
      (groupCohomology.H0Iso Y.X₃).hom =
        (groupCohomology.H0Iso Y.X₂).hom ≫
          (Rep.invariantsFunctor k H).map Y.g :=
    groupCohomology.map_id_comp_H0Iso_hom Y.g
  haveI hcomp : Epi (q ≫ (groupCohomology.H0Iso Y.X₃).hom) :=
    epi_comp _ _
  haveI hinv : Epi
      ((Rep.invariantsFunctor k H).map Y.g) := by
    refine ⟨fun a b hab => ?_⟩
    apply hcomp.left_cancellation a b
    rw [hnat]
    simpa only [Category.assoc] using
      congrArg (fun t => (groupCohomology.H0Iso Y.X₂).hom ≫ t) hab
  haveI hepi : Epi (F.map X.g) := by
    rw [Rep.epi_iff_surjective]
    exact (ModuleCat.epi_iff_surjective _).1 hinv
  haveI hmono : Mono (F.map X.f) := by
    rw [Rep.mono_iff_injective]
    intro a b hab
    apply Subtype.ext
    apply (Rep.mono_iff_injective X.f).1 hX.mono_f
    exact congrArg Subtype.val hab
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ hX.fIsKernel F)) hmono hepi

end Adjunction

section AcyclicInflation

variable [Finite G]

set_option maxHeartbeats 2000000 in
-- The recursive construction elaborates several mapped short exact sequences.
/-- If the positive-degree cohomology of a normal subgroup vanishes, then
passing to invariants and quotienting the group does not change positive
cohomology.  This is the acyclic form of Proposition II.1.34 used in Milne's
proof of Theorem II.3.10. -/
theorem inflation_acyclic_nonempty
    (A : Rep.{u} k G) (H : Subgroup G) [H.Normal]
    (hH : ∀ q : ℕ, 0 < q →
      IsZero (groupCohomology (Rep.res H.subtype A) q))
    (n : ℕ) (hn : 0 < n) :
    Nonempty (groupCohomology (A.quotientToInvariants H) n ≅
      groupCohomology A n) := by
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
      cases n with
      | zero => exact (Nat.not_lt_zero 0 hn).elim
      | succ m =>
          by_cases hm : m = 0
          · subst m
            let C := groupCohomology.H1InfRes A H
            haveI hfmono : Mono C.f := by
              change Mono (groupCohomology.H1InfRes A H).f
              infer_instance
            have hexact : C.Exact := groupCohomology.H1InfRes_exact A H
            have hgzero : C.g = 0 := by
              exact (hH 1 Nat.zero_lt_one).eq_of_tgt _ _
            haveI hfepi : Epi C.f := hexact.epi_f hgzero
            haveI hfiso : IsIso C.f := isIso_of_mono_of_epi C.f
            exact ⟨@asIso _ _ _ _ C.f hfiso⟩
          · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
            let ⟨p⟩ := EnoughInjectives.presentation A
            let X : ShortComplex (Rep.{u} k G) :=
              ShortComplex.cokernelSequence p.f
            have hX : X.ShortExact := {
              exact := ShortComplex.cokernelSequence_exact p.f
              mono_f := p.mono
              epi_g := inferInstance }
            letI : Injective X.X₂ := p.injective
            have hmiddleG : ∀ q : ℕ, 0 < q →
                IsZero (groupCohomology X.X₂ q) := by
              intro q hq
              exact zero_cohomology_injective X.X₂ q hq
            let deltaG := dimensionShiftingIso hX hmiddleG m hmpos
            let XH := X.map (Rep.resFunctor H.subtype)
            have hXH : XH.ShortExact :=
              hX.map_of_exact (Rep.resFunctor H.subtype)
            letI := Classical.decRel (QuotientGroup.rightRel H)
            letI : PreservesLimitsOfSize.{0, 0}
                (Rep.indFunctor k H.subtype) :=
              (Rep.resIndAdjunction k H).rightAdjoint_preservesLimits
            letI : Injective XH.X₂ :=
              (Rep.indResAdjunction k H.subtype).map_injective X.X₂ inferInstance
            have hmiddleH : ∀ q : ℕ, 0 < q →
                IsZero (groupCohomology XH.X₂ q) := by
              intro q hq
              exact zero_cohomology_injective XH.X₂ q hq
            have hX3H : ∀ q : ℕ, 0 < q →
                IsZero (groupCohomology (Rep.res H.subtype X.X₃) q) := by
              intro q hq
              have htarget := hH (q + 1) (Nat.succ_pos q)
              exact htarget.of_iso
                (dimensionShiftingIso hXH hmiddleH q hq)
            let F := Rep.quotientToInvariantsFunctor.{u} k H
            let XQ := X.map F
            have hXQ : XQ.ShortExact :=
              invariants_short_exact H hX (hH 1 Nat.zero_lt_one)
            letI : Injective XQ.X₂ :=
              quotient_invariants_injective H X.X₂
            have hmiddleQ : ∀ q : ℕ, 0 < q →
                IsZero (groupCohomology XQ.X₂ q) := by
              intro q hq
              exact zero_cohomology_injective XQ.X₂ q hq
            let deltaQ := dimensionShiftingIso hXQ hmiddleQ m hmpos
            let shiftedIso :=
              (ih m (Nat.lt_succ_self m) X.X₃ hX3H hmpos).some
            exact ⟨deltaQ.symm ≪≫ shiftedIso ≪≫ deltaG⟩

/-- A chosen cohomology isomorphism across a cohomologically acyclic normal
subgroup.  Its existence is Proposition II.1.34 plus dimension shifting. -/
noncomputable def inflationIsoAcyclic
    (A : Rep.{u} k G) (H : Subgroup G) [H.Normal]
    (hH : ∀ q : ℕ, 0 < q →
      IsZero (groupCohomology (Rep.res H.subtype A) q))
    (n : ℕ) (hn : 0 < n) :
    groupCohomology (A.quotientToInvariants H) n ≅
      groupCohomology A n :=
  (inflation_acyclic_nonempty A H hH n hn).some

end AcyclicInflation

end

end Towers.CField.COps
