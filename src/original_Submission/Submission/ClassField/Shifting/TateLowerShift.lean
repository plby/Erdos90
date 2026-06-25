import Submission.ClassField.Shifting.TateCover
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-!
# Milne, Class Field Theory, Theorem II.3.10: lower Tate shifts

The induced middle term in Milne's cover has vanishing positive group
homology.  Consequently the homology connecting morphisms give the repeated
dimension shifts used for Tate degrees below minus two.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Finite G]

/-- The middle term of Milne's cover has vanishing positive group homology. -/
theorem cover_homology_acyclic
    (A : Rep.{u} k G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupHomology (coverMiddle A) n) := by
  let B := Rep.res (⊥ : Subgroup G).subtype A
  have hInd : IsZero
      (groupHomology (Rep.ind (⊥ : Subgroup G).subtype B) n) :=
    zero_homology_induced B n hn
  exact hInd.of_iso
    ((groupHomology.functor k G n).mapIso
      (coverMiddleInduced A).symm)

/-- The positive-homology part of Milne's repeated negative dimension shift:
`H_(n+1)(G,A) ≅ H_n(G,A')` for `n > 0`. -/
noncomputable def coverHomologyShift
    (A : Rep.{u} k G) (n : ℕ) (hn : 0 < n) :
    groupHomology A (n + 1) ≅
      groupHomology (coverSequence A).X₁ n := by
  let X := coverSequence A
  let hX : X.ShortExact := cover_sequence_short A
  let d := groupHomology.δ hX (n + 1) n rfl
  let hd : IsIso d :=
    groupHomology.isIso_δ_of_isZero hX n
      (cover_homology_acyclic A (n + 1) (by omega))
      (cover_homology_acyclic A n hn)
  exact @asIso _ _ _ _ d hd

/-- The low-degree homology boundary, viewed in the kernel of the norm. -/
noncomputable def homologyBoundaryNeg [Fintype G]
    (X : ShortComplex (Rep.{u} k G)) (hX : X.ShortExact) :
    groupHomology X.X₃ 1 →ₗ[k] tateCohomologyOne X.X₁ :=
  ((groupHomology.δ hX 1 0 rfl ≫ (groupHomology.H0Iso X.X₁).hom).hom).codRestrict
    (LinearMap.ker (normCoinvariantsInvariants X.X₁)) fun x ↦ by
      rw [LinearMap.mem_ker]
      let F := Rep.coinvariantsFunctor.{u} k G
      let I := Rep.invariantsFunctor.{u} k G
      let v := normNatTrans (k := k) (G := G)
      let y : F.obj X.X₁ :=
        (groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl x)
      have hzeroH₀ :
          (groupHomology.mapShortComplex₁ hX rfl).g
            (groupHomology.δ hX 1 0 rfl x) = 0 := by
        change ((groupHomology.mapShortComplex₁ hX rfl).f ≫
          (groupHomology.mapShortComplex₁ hX rfl).g) x = 0
        rw [(groupHomology.mapShortComplex₁ hX rfl).zero]
        rfl
      have hy : F.map X.f y = 0 := by
        calc
          F.map X.f y = (groupHomology.H0Iso X.X₂).hom
              ((groupHomology.mapShortComplex₁ hX rfl).g
                (groupHomology.δ hX 1 0 rfl x)) :=
            (congrArg (fun q => q (groupHomology.δ hX 1 0 rfl x))
              (groupHomology.map_id_comp_H0Iso_hom X.f)).symm
          _ = 0 := by
            rw [hzeroH₀]
            exact (groupHomology.H0Iso X.X₂).hom.hom.map_zero
      have hInvInjective : Function.Injective (I.map X.f) := by
        intro a b hab
        apply Subtype.ext
        apply (Rep.mono_iff_injective X.f).1 hX.mono_f
        exact Subtype.ext_iff.mp hab
      have hnat : F.map X.f ≫ v.app X.X₂ =
          v.app X.X₁ ≫ I.map X.f := v.naturality X.f
      change v.app X.X₁ y = 0
      apply hInvInjective
      calc
        I.map X.f (v.app X.X₁ y) = v.app X.X₂ (F.map X.f y) :=
          (congrArg (fun q => q y) hnat).symm
        _ = 0 := by rw [hy, map_zero]
        _ = I.map X.f 0 := (map_zero _).symm

/-- The lower exceptional boundary is an equivalence when the middle first
homology and degree-minus-one Tate group vanish. -/
noncomputable def homologyNegShort [Fintype G]
    (X : ShortComplex (Rep.{u} k G)) (hX : X.ShortExact)
    (hH₁ : IsZero (groupHomology X.X₂ 1))
    (hneg : Subsingleton (tateCohomologyOne X.X₂)) :
    groupHomology X.X₃ 1 ≃ₗ[k] tateCohomologyOne X.X₁ := by
  apply LinearEquiv.ofBijective (homologyBoundaryNeg X hX)
  constructor
  · intro x y hxy
    have hdelta : groupHomology.δ hX 1 0 rfl x =
        groupHomology.δ hX 1 0 rfl y := by
      apply (ModuleCat.mono_iff_injective (groupHomology.H0Iso X.X₁).hom).1
        inferInstance
      exact congrArg Subtype.val hxy
    exact (ModuleCat.mono_iff_injective (groupHomology.δ hX 1 0 rfl)).1
      (groupHomology.mono_δ_of_isZero hX 0 hH₁) hdelta
  · rintro ⟨z, hz⟩
    let F := Rep.coinvariantsFunctor.{u} k G
    let I := Rep.invariantsFunctor.{u} k G
    let v := normNatTrans (k := k) (G := G)
    have hnorm₂ : Function.Injective (normCoinvariantsInvariants X.X₂) :=
      (norm_coinvariants_invariants X.X₂).2 hneg
    have hfzero : F.map X.f z = 0 := by
      apply hnorm₂
      have hnat : F.map X.f ≫ v.app X.X₂ =
          v.app X.X₁ ≫ I.map X.f := v.naturality X.f
      change v.app X.X₂ (F.map X.f z) = v.app X.X₂ 0
      calc
        v.app X.X₂ (F.map X.f z) = I.map X.f (v.app X.X₁ z) :=
          congrArg (fun q => q z) hnat
        _ = 0 := by
          rw [show v.app X.X₁ z = 0 from LinearMap.mem_ker.mp hz, map_zero]
        _ = v.app X.X₂ 0 := (map_zero _).symm
    let z₀ : groupHomology X.X₁ 0 := (groupHomology.H0Iso X.X₁).inv z
    have hmapzero :
        (groupHomology.mapShortComplex₁ hX rfl).g z₀ = 0 := by
      apply (ModuleCat.mono_iff_injective (groupHomology.H0Iso X.X₂).hom).1
        inferInstance
      calc
        (groupHomology.H0Iso X.X₂).hom
            ((groupHomology.mapShortComplex₁ hX rfl).g z₀) =
            F.map X.f ((groupHomology.H0Iso X.X₁).hom z₀) :=
          congrArg (fun q => q z₀)
            (groupHomology.map_id_comp_H0Iso_hom X.f)
        _ = F.map X.f z := by simp only [z₀, Iso.inv_hom_id_apply]
        _ = 0 := hfzero
        _ = (groupHomology.H0Iso X.X₂).hom 0 := (map_zero _).symm
    let S := groupHomology.mapShortComplex₁ (i := 1) (j := 0) hX rfl
    have hexact : Function.Exact S.f S.g :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp
        (groupHomology.mapShortComplex₁_exact (i := 1) (j := 0) hX rfl)
    obtain ⟨x, hx⟩ := (hexact z₀).mp hmapzero
    refine ⟨x, Subtype.ext ?_⟩
    change (groupHomology.H0Iso X.X₁).hom (S.f x) = z
    rw [hx]
    exact Iso.inv_hom_id_apply (groupHomology.H0Iso X.X₁) z

/-- The first homology group of a module is the degree-minus-one Tate group
of the kernel of Milne's cover. -/
noncomputable def coverOneShift [Fintype G]
    (A : Rep.{u} k G) :
    groupHomology A 1 ≃ₗ[k]
      tateCohomologyOne (coverSequence A).X₁ := by
  let B := Rep.res (⊥ : Subgroup G).subtype A
  letI : DecidableRel (QuotientGroup.rightRel (⊥ : Subgroup G)) :=
    Classical.decRel _
  let e : coverMiddle A ≅
      Rep.ind (⊥ : Subgroup G).subtype B :=
    (coverMiddleInduced A).symm
  have hnegInd : Subsingleton
      (tateCohomologyOne (Rep.ind (⊥ : Subgroup G).subtype B)) :=
    subsingleton_cohomology_induced B
  have hnegMiddle : Subsingleton
      (tateCohomologyOne (coverMiddle A)) :=
    (norm_coinvariants_invariants _).1
      (coinvariants_injective_iso e
        ((norm_coinvariants_invariants _).2 hnegInd))
  exact homologyNegShort
    (coverSequence A) (cover_sequence_short A)
    (cover_homology_acyclic A 1 Nat.zero_lt_one)
    hnegMiddle

end

end Submission.CField.Shifting
