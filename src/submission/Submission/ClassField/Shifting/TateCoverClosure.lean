import Submission.ClassField.Shifting.TateCover
import Submission.ClassField.Shifting.TransportAlongEquivalences

/-!
# Milne, Class Field Theory, Theorem II.3.10: cover-kernel closure

This file proves that the kernel of Milne's induced cover again satisfies the
degree-one and degree-two vanishing hypothesis.  The degree-one proof uses the
low-degree cohomology sequence and norm surjectivity; degree two is the usual
positive dimension shift.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- If `H_T⁰(H,A)` vanishes, then the kernel `A'` of Milne's induced
cover has vanishing `H¹(H,A')`. -/
theorem cohomology_cover_kernel [Finite G]
    (A : Rep.{u} k G) (H : Subgroup G) [Fintype H]
    (hzero : Subsingleton (tateCohomologyZero (Rep.res H.subtype A))) :
    IsZero (groupCohomology
      (Rep.res H.subtype (coverSequence A).X₁) 1) := by
  let X := (coverSequence A).map (Rep.resFunctor H.subtype)
  have hX : X.ShortExact := cover_short_exact A H
  let F := Rep.coinvariantsFunctor.{u} k H
  let I := Rep.invariantsFunctor.{u} k H
  let v := normNatTrans (k := k) (G := H)
  have hgSurj : Function.Surjective X.g.hom :=
    (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hcoinvSurj : Function.Surjective (F.map X.g) := by
    intro c
    obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective X.X₃.ρ c
    obtain ⟨b, hb⟩ := hgSurj a
    refine ⟨Representation.Coinvariants.mk X.X₂.ρ b, ?_⟩
    change Representation.Coinvariants.mk X.X₃.ρ (X.g.hom b) =
      Representation.Coinvariants.mk X.X₃.ρ a
    rw [hb]
  haveI hepiCoinv : Epi (F.map X.g) :=
    (ModuleCat.epi_iff_surjective _).2 hcoinvSurj
  haveI hepiNorm : Epi (v.app X.X₃) :=
    (ModuleCat.epi_iff_surjective _).2
      ((coinvariants_invariants_surjective X.X₃).2 hzero)
  haveI hepiTop : Epi (F.map X.g ≫ v.app X.X₃) :=
    epi_comp' hepiCoinv hepiNorm
  have hnat : F.map X.g ≫ v.app X.X₃ =
      v.app X.X₂ ≫ I.map X.g := v.naturality X.g
  haveI hepiBottom : Epi (v.app X.X₂ ≫ I.map X.g) := by
    rw [← hnat]
    exact hepiTop
  haveI hepiInv : Epi (I.map X.g) := epi_of_epi (v.app X.X₂) (I.map X.g)
  let q :=
    (groupCohomology.mapShortComplex₃ (i := 0) (j := 1) hX rfl).f
  have hqnat : q ≫ (groupCohomology.H0Iso X.X₃).hom =
      (groupCohomology.H0Iso X.X₂).hom ≫ I.map X.g :=
    groupCohomology.map_id_comp_H0Iso_hom X.g
  haveI hepiH0 : Epi (groupCohomology.H0Iso X.X₂).hom := inferInstance
  haveI hepiRhs : Epi
      ((groupCohomology.H0Iso X.X₂).hom ≫ I.map X.g) :=
    epi_comp' hepiH0 hepiInv
  haveI hepiQComp : Epi (q ≫ (groupCohomology.H0Iso X.X₃).hom) := by
    rw [hqnat]
    exact hepiRhs
  haveI hepiQ : Epi q :=
    (epi_comp_iff_of_isIso q (groupCohomology.H0Iso X.X₃).hom).mp
      hepiQComp
  let d := groupCohomology.δ hX 0 1 rfl
  haveI hepiDelta : Epi d :=
    groupCohomology.epi_δ_of_isZero hX 0
      (cover_middle_acyclic A H 1 Nat.zero_lt_one)
  have hdelta : d = 0 := zero_of_epi_comp q
    (groupCohomology.mapShortComplex₃ (i := 0) (j := 1) hX rfl).zero
  exact @IsZero.of_epi_eq_zero _ _ _ _ _ d hepiDelta hdelta

/-- The positive dimension shift identifies `H²(H,A')` with `H¹(H,A)`
for the kernel of Milne's induced cover. -/
theorem zero_cohomology_cover [Finite G]
    (A : Rep.{u} k G) (H : Subgroup G)
    (hone : IsZero (groupCohomology (Rep.res H.subtype A) 1)) :
    IsZero (groupCohomology
      (Rep.res H.subtype (coverSequence A).X₁) 2) :=
  hone.of_iso (coverCohomologyShift A H 1 Nat.zero_lt_one).symm

/-- The kernel of Milne's induced cover again has vanishing `H¹` and `H²`
over a subgroup whenever `H_T⁰` and `H¹` vanish there for the original
module. -/
theorem cover_12_subgroup [Finite G]
    (A : Rep.{u} k G) (H : Subgroup G) [Fintype H]
    (hzero : Subsingleton (tateCohomologyZero (Rep.res H.subtype A)))
    (hone : IsZero (groupCohomology (Rep.res H.subtype A) 1)) :
    IsZero (groupCohomology
        (Rep.res H.subtype (coverSequence A).X₁) 1) ∧
      IsZero (groupCohomology
        (Rep.res H.subtype (coverSequence A).X₁) 2) :=
  ⟨cohomology_cover_kernel A H hzero,
    zero_cohomology_cover A H hone⟩

/-- The cover-kernel closure result for an arbitrary injective homomorphism.
Factoring through the range shows that this is equivalent to the subgroup
form used in Milne's statement. -/
theorem cover_12_injective {K : Type u} [Group K] [Finite G]
    (A : Rep.{u} k G) (f : K →* G) [Fintype K]
    (hf : Function.Injective f)
    (hzero : Subsingleton (tateCohomologyZero (Rep.res f A)))
    (hone : IsZero (groupCohomology (Rep.res f A) 1)) :
    IsZero (groupCohomology
        (Rep.res f (coverSequence A).X₁) 1) ∧
      IsZero (groupCohomology
        (Rep.res f (coverSequence A).X₁) 2) := by
  letI : Fintype f.range := Fintype.ofFinite f.range
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  let AR := Rep.res f.range.subtype A
  have hzeroE : Subsingleton
      (tateCohomologyZero (Rep.res e.toMonoidHom AR)) := by
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def, e, AR]
      using hzero
  have honeE : IsZero
      (groupCohomology (Rep.res e.toMonoidHom AR) 1) := by
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def, e, AR]
      using hone
  have hzeroR : Subsingleton (tateCohomologyZero AR) :=
    subsingleton_tate_cohomology e AR hzeroE
  have honeR : IsZero (groupCohomology AR 1) :=
    honeE.of_iso (cohomologyMulIso e AR 1)
  have hR := cover_12_subgroup A f.range hzeroR honeR
  constructor
  · have h := hR.1.of_iso
        (cohomologyMulIso e
          (Rep.res f.range.subtype (coverSequence A).X₁) 1).symm
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def, e] using h
  · have h := hR.2.of_iso
        (cohomologyMulIso e
          (Rep.res f.range.subtype (coverSequence A).X₁) 2).symm
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def, e] using h

end

end Submission.CField.Shifting
