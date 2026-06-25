import Towers.ClassField.CohomologyOps.CoindHomApply
import Towers.ClassField.CohomologyOps.ShortComplexMap
import Towers.ClassField.LocalReciprocity.NormResidueFormula
import Towers.ClassField.ReciprocityExistence.CyclicCarryTransport

/-!
# Tate--Nakayama adjointness for Proposition III.3.6

This file supplies the low-degree compatibility between the degree-minus-two
Tate shift and cup product with a character boundary.
-/

namespace Towers.CField.LRecip

open CategoryTheory Rep
open Towers.CField.COps
open Towers.CField.COps.CPFuncto
open Towers.CField.COps.CPBuild
open Towers.CField.Shifting
open Towers.CField.RExist

noncomputable section

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {G : Type} [Group G] [Fintype G]

local instance (priority := 10000) repIntModule
    {J : Type} [Group J] (A : Rep.{0} ℤ J) : Module ℤ A := A.hV2

/-- An invariant coefficient as a degree-zero class. -/
private noncomputable def invariantH0
    {k J : Type} [CommRing k] [Group J] (A : Rep.{0} k J)
    (m : A.ρ.invariants) : groupCohomology A 0 :=
  groupCohomology.π A 0 ((groupCohomology.cocyclesIso₀ A).inv m)

/-- Evaluation at one identifies invariant coinduced functions with the
invariants of the subgroup representation. -/
private def coinducedInvariantsEquiv
    {k J : Type} [CommRing k] [Group J]
    (H : Subgroup J) (B : Rep.{0} k H) :
    (Rep.coind.{0, 0, 0, 0} H.subtype B).ρ.invariants ≃ B.ρ.invariants where
  toFun x := ⟨x.1.1 1, fun h => by
    have hx := congrArg (fun f => f.1 1) (x.2 (h : J))
    calc
      B.ρ h (x.1.1 1) = x.1.1 h := by
        simpa using (x.1.2 h 1).symm
      _ = x.1.1 1 := by simpa [Representation.coind] using hx⟩
  invFun m := ⟨⟨fun _ => m.1, fun h g => by simpa using (m.2 h).symm⟩,
    fun g => by apply Subtype.ext; funext t; rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have hx := congrArg (fun f => f.1 1) (x.2 g)
    simpa [Representation.coind] using hx.symm
  right_inv _ := rfl

private def restrictInvariant
    {k J : Type} [CommRing k] [Group J]
    (A : Rep.{0} k J) (H : Subgroup J) (m : A.ρ.invariants) :
    (Rep.res H.subtype A).ρ.invariants :=
  ⟨m.1, fun h => by simpa using m.2 (h : J)⟩

private theorem cocyclesIso₀_hom_coe
    {k J : Type} [CommRing k] [Group J]
    (A : Rep.{0} k J) (x : groupCohomology.cocycles A 0) :
    ((groupCohomology.cocyclesIso₀ A).hom x).1 =
      groupCohomology.iCocycles A 0 x (fun i => Fin.elim0 i) := by
  have h := congrArg (fun q => q x)
    (groupCohomology.cocyclesIso₀_hom_comp_f A)
  simpa only [ConcreteCategory.comp_apply] using h

private theorem restriction_0_hom
    {J : Type} [Group J]
    (A : Rep.{0} ℤ J) (H : Subgroup J) (x : groupCohomology A 0) :
    (groupCohomology.H0Iso (Rep.res H.subtype A)).hom
        (restriction A H 0 x) =
      restrictInvariant A H ((groupCohomology.H0Iso A).hom x) := by
  induction x using groupCohomology_induction_on with
  | h xc =>
      have hmap := congrArg (fun q => q xc)
        (groupCohomology.π_map H.subtype (𝟙 (Rep.res H.subtype A)) 0)
      simp only [ConcreteCategory.comp_apply] at hmap
      change (groupCohomology.H0Iso (Rep.res H.subtype A)).hom
          (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype A)) 0
            (groupCohomology.π A 0 xc)) = _
      rw [hmap, groupCohomology.π_comp_H0Iso_hom_apply,
        groupCohomology.π_comp_H0Iso_hom_apply]
      apply Subtype.ext
      have hi := CPFuncto.i_cocycles_restrict
        H.subtype A 0 xc
      simp only [restrictInvariant]
      rw [cocyclesIso₀_hom_coe, cocyclesIso₀_hom_coe]
      change groupCohomology.iCocycles (Rep.res H.subtype A) 0
          (groupCohomology.cocyclesMap H.subtype
            (𝟙 (Rep.res H.subtype A)) 0 xc) (fun i => Fin.elim0 i) =
        groupCohomology.iCocycles A 0 xc (fun i => Fin.elim0 i)
      rw [congrFun hi (fun i => Fin.elim0 i)]
      apply congrArg (groupCohomology.iCocycles A 0 xc)
      funext i
      exact Fin.elim0 i

private theorem coind_iso_0
    {J : Type} [Group J]
    (H : Subgroup J) (B : Rep.{0} ℤ H)
    (z : groupCohomology B 0) :
    (coinducedInvariantsEquiv H B
        ((groupCohomology.H0Iso (Rep.coind.{0, 0, 0, 0} H.subtype B)).hom
          ((groupCohomology.coindIso B 0).inv z))).1 =
      ((groupCohomology.H0Iso B).hom z).1 := by
  let w := (groupCohomology.coindIso B 0).inv z
  have hz := congrArg (fun f => f w)
    (coind_iso_counit H B 0)
  simp only at hz
  have hz' : groupCohomology.map (MonoidHom.id H)
      ((resCoindAdjunction ℤ H.subtype).counit.app B) 0
      (restriction (Rep.coind.{0, 0, 0, 0} H.subtype B) H 0 w) = z := by
    calc
      _ = (groupCohomology.coindIso B 0).hom w := hz.symm
      _ = z := by simp [w]
  let wInv := (groupCohomology.H0Iso
    (Rep.coind.{0, 0, 0, 0} H.subtype B)).hom w
  have hres := restriction_0_hom
    (Rep.coind.{0, 0, 0, 0} H.subtype B) H w
  have hnat := congrArg (fun f => f (restriction
    (Rep.coind.{0, 0, 0, 0} H.subtype B) H 0 w))
    (groupCohomology.map_id_comp_H0Iso_hom
      ((resCoindAdjunction ℤ H.subtype).counit.app B))
  have hnat'' : (groupCohomology.H0Iso B).hom
      (groupCohomology.map (MonoidHom.id H)
        ((resCoindAdjunction ℤ H.subtype).counit.app B) 0
        (restriction (Rep.coind.{0, 0, 0, 0} H.subtype B) H 0 w)) =
      (Rep.invariantsFunctor ℤ H).map
        ((resCoindAdjunction ℤ H.subtype).counit.app B)
        ((groupCohomology.H0Iso
          (Rep.res H.subtype (Rep.coind.{0, 0, 0, 0} H.subtype B))).hom
          (restriction (Rep.coind.{0, 0, 0, 0} H.subtype B) H 0 w)) := by
    simpa only [ConcreteCategory.comp_apply] using hnat
  have hnat' := (congrArg (fun q =>
    (groupCohomology.H0Iso B).hom q) hz').symm.trans hnat''
  rw [hres] at hnat'
  change (wInv.1.1 1) = _
  have hv :
      (((Rep.invariantsFunctor ℤ H).map
        ((resCoindAdjunction ℤ H.subtype).counit.app B))
        (restrictInvariant
          (Rep.coind.{0, 0, 0, 0} H.subtype B) H wInv)).1 =
        wInv.1.1 1 := rfl
  exact hv.symm.trans (congrArg Subtype.val hnat'.symm)

set_option maxHeartbeats 1000000 in
-- Expanding corestriction in degree zero and comparing the two quotient
-- transversals creates a large categorical normalization proof.
omit [Fintype G] in
/-- In degree zero the cohomological corestriction is the usual transversal
norm on invariant representatives. -/
theorem corestriction_0_transversal
    (A : Rep.{0} ℤ G) (H : Subgroup G) [H.FiniteIndex]
    (S : H.LeftTransversal)
    (m : groupCohomology.cocycles (Rep.res H.subtype A) 0) :
    corestriction A H 0
        (groupCohomology.π (Rep.res H.subtype A) 0 m) =
      groupCohomology.π A 0 ((groupCohomology.cocyclesIso₀ A).inv
        (let m' := (groupCohomology.cocyclesIso₀
          (Rep.res H.subtype A)).hom m
        ⟨transversalNorm A H S m'.1,
          transversal_norm_invariants A H m'.1 m'.2 S⟩)) := by
  apply (ModuleCat.mono_iff_injective (groupCohomology.H0Iso A).hom).1
    inferInstance
  let m' := (groupCohomology.cocyclesIso₀
    (Rep.res H.subtype A)).hom m
  let z := groupCohomology.π (Rep.res H.subtype A) 0 m
  let fInv := (groupCohomology.H0Iso
    (Rep.coind.{0, 0, 0, 0} H.subtype (Rep.res H.subtype A))).hom
      ((groupCohomology.coindIso (Rep.res H.subtype A) 0).inv z)
  rw [corestriction]
  simp only [ConcreteCategory.comp_apply]
  rw [groupCohomology.π_comp_H0Iso_hom_apply]
  change (groupCohomology.H0Iso A).hom
      (groupCohomology.map (MonoidHom.id G) (corestrictionTrace A H) 0
        ((groupCohomology.coindIso (Rep.res H.subtype A) 0).inv z)) =
    (groupCohomology.cocyclesIso₀ A).hom
      ((groupCohomology.cocyclesIso₀ A).inv
        ⟨transversalNorm A H S m'.1,
          transversal_norm_invariants A H m'.1 m'.2 S⟩)
  rw [groupCohomology.map_id_comp_H0Iso_hom_apply,
    Iso.inv_hom_id_apply]
  change ((Rep.invariantsFunctor ℤ G).map (corestrictionTrace A H)) fInv =
    ⟨transversalNorm A H S m'.1,
      transversal_norm_invariants A H m'.1 m'.2 S⟩
  have hf : fInv =
      (coinducedInvariantsEquiv H (Rep.res H.subtype A)).symm m' := by
    apply (coinducedInvariantsEquiv H (Rep.res H.subtype A)).injective
    apply Subtype.ext
    calc
      ((coinducedInvariantsEquiv H (Rep.res H.subtype A)) fInv).1 =
          ((groupCohomology.H0Iso (Rep.res H.subtype A)).hom z).1 :=
        coind_iso_0 H (Rep.res H.subtype A) z
      _ = m'.1 := by
        dsimp only [z, m']
        rw [groupCohomology.π_comp_H0Iso_hom_apply]
      _ = ((coinducedInvariantsEquiv H (Rep.res H.subtype A))
          ((coinducedInvariantsEquiv H (Rep.res H.subtype A)).symm m')).1 := by
        rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  change (corestrictionTrace A H).hom fInv.1 =
    transversalNorm A H S m'.1
  rw [hf, corestrictionTrace_apply]
  let invEquiv : G ≃ G :=
    { toFun := Inv.inv
      invFun := Inv.inv
      left_inv := inv_inv
      right_inv := inv_inv }
  let e : Quotient (QuotientGroup.rightRel H) ≃ G ⧸ H :=
    Quotient.congr invEquiv (by
      intro x y
      rw [QuotientGroup.rightRel_apply, QuotientGroup.leftRel_apply]
      constructor
      · intro h
        dsimp only [invEquiv, Equiv.coe_fn_mk]
        rw [inv_inv]
        simpa [mul_inv_rev] using H.inv_mem h
      · intro h
        dsimp only [invEquiv, Equiv.coe_fn_mk] at h ⊢
        rw [inv_inv] at h
        change x * y⁻¹ ∈ H at h
        simpa [mul_inv_rev] using H.inv_mem h)
  rw [transversalNorm]
  apply Fintype.sum_equiv e
  intro q
  let r : G := (Quotient.out q)⁻¹
  let s : G := S.2.leftQuotientEquiv (e q)
  have hr : Quotient.mk'' r = e q := by
    rw [show q = Quotient.mk'' q.out from (Quotient.out_eq' q).symm]
    rfl
  have hs : Quotient.mk'' s = e q :=
    S.2.quotientGroupMk_leftQuotientEquiv (e q)
  have hrs : r⁻¹ * s ∈ H := by
    rw [← QuotientGroup.leftRel_apply]
    exact Quotient.exact' (hr.trans hs.symm)
  let h : H := ⟨r⁻¹ * s, hrs⟩
  have hsr : s = r * h := by simp [h]
  change A.ρ r m'.1 = A.ρ s m'.1
  have hm : A.ρ (h : G) m'.1 = m'.1 := m'.2 h
  calc
    A.ρ r m'.1 = A.ρ r (A.ρ h m'.1) := by
      rw [hm]
    _ = A.ρ (r * h) m'.1 :=
      CPBuild.rep_action_mul A r (h : G) m'.1
    _ = A.ρ s m'.1 := by rw [hsr]

/-- Cupping a norm invariant with a positive-degree class gives zero.  This
is the degree-zero projection formula, expressed using the inhomogeneous cup
product used by Proposition III.3.6. -/
theorem cup_cohomology_invariant
    (C : Rep.{0} ℤ G) (x : C)
    (y : groupCohomology (Rep.trivial ℤ G ℤ) 2) :
    cupCohomology C (Rep.trivial ℤ G ℤ) 0 2
        (invariantH0 C
          ⟨C.ρ.norm x, fun g => C.ρ.self_norm_apply g x⟩) y = 0 := by
  let H : Subgroup G := ⊥
  letI : Fintype H := Fintype.ofFinite H
  let S : H.LeftTransversal :=
    ⟨Set.range (fun q : G ⧸ H => q.out),
      Subgroup.isComplement_range_left Quotient.out_eq'⟩
  let mH : (Rep.res H.subtype C).ρ.invariants :=
    ⟨(Rep.res H.subtype C).ρ.norm x,
      fun h => (Rep.res H.subtype C).ρ.self_norm_apply h x⟩
  let cH : groupCohomology.cocycles (Rep.res H.subtype C) 0 :=
    (groupCohomology.cocyclesIso₀ (Rep.res H.subtype C)).inv mH
  have hcor := corestriction_0_transversal C H S cH
  have hnorm := corestriction_norm_restrict C H S x
  have htrans :
      (⟨transversalNorm C H S mH.1,
        transversal_norm_invariants C H mH.1 mH.2 S⟩ : C.ρ.invariants) =
      ⟨C.ρ.norm x, fun g => C.ρ.self_norm_apply g x⟩ := by
    simpa [COps.corestrictionZero, mH] using hnorm
  have hcor' : corestriction C H 0
      (invariantH0 (Rep.res H.subtype C) mH) =
      invariantH0 C ⟨C.ρ.norm x,
        fun g => C.ρ.self_norm_apply g x⟩ := by
    rw [← htrans]
    simpa [invariantH0, cH, mH] using hcor
  have hy : restriction (Rep.trivial ℤ G ℤ) H 2 y = 0 := by
    letI : Subsingleton H := ⟨fun a b => Subtype.ext
      (Subgroup.mem_bot.mp a.2 |>.trans (Subgroup.mem_bot.mp b.2).symm)⟩
    exact (ModuleCat.subsingleton_of_isZero
      (isZero_groupCohomology_succ_of_subsingleton
        (Rep.res H.subtype (Rep.trivial ℤ G ℤ)) 1)).elim _ _
  have hproj := cup_corestriction_projection H C
    (Rep.trivial ℤ G ℤ) 0 2 (invariantH0 (Rep.res H.subtype C) mH) y
  rw [hy, map_zero, hcor'] at hproj
  rw [← hproj]
  exact map_zero _

/-- Restricting a character boundary to a subgroup gives the boundary of
the restricted character. -/
theorem restriction_characterBoundary (H : Subgroup G) [Fintype H]
    (chi : RationalCharacter G) :
    restriction (Rep.trivial ℤ G ℤ) H 2 (characterBoundary G chi) =
      characterBoundary H (chi.comp H.subtype.toAdditive) := by
  let z : groupCohomology (Rep.trivial ℤ G rationalModIntegers) 1 :=
    groupCohomology.H1π (Rep.trivial ℤ G rationalModIntegers)
      ((groupCohomology.cocycles₁IsoOfIsTrivial
        (Rep.trivial ℤ G rationalModIntegers)).inv
          (characterRationalIntegers G chi))
  have hdelta := congrArg (fun f => f z)
    (restriction_delta_naturality
      (sequence_short_exact G) H 1)
  simp only [ConcreteCategory.comp_apply] at hdelta
  change restriction (Rep.trivial ℤ G ℤ) H 2
      (groupCohomology.δ (sequence_short_exact G)
        1 2 rfl z) = _
  have hdelta' : restriction (Rep.trivial ℤ G ℤ) H 2
        (groupCohomology.δ (sequence_short_exact G)
          1 2 rfl z) =
      groupCohomology.δ
        ((sequence_short_exact G).map_of_exact
          (Rep.resFunctor H.subtype)) 1 2 rfl
        (restriction (Rep.trivial ℤ G rationalModIntegers) H 1 z) := by
    simpa [restriction] using hdelta
  rw [hdelta']
  rw [characterBoundary]
  change groupCohomology.δ
      ((sequence_short_exact G).map_of_exact
        (Rep.resFunctor H.subtype)) 1 2 rfl
        (restriction (Rep.trivial ℤ G rationalModIntegers) H 1 z) =
    groupCohomology.δ (sequence_short_exact H)
      1 2 rfl
      (groupCohomology.H1π (Rep.trivial ℤ H rationalModIntegers)
        ((groupCohomology.cocycles₁IsoOfIsTrivial
          (Rep.trivial ℤ H rationalModIntegers)).inv
            (characterRationalIntegers H
              (chi.comp H.subtype.toAdditive))))
  congr 1
  let cG := (groupCohomology.cocycles₁IsoOfIsTrivial
    (Rep.trivial ℤ G rationalModIntegers)).inv
      (characterRationalIntegers G chi)
  let cH := (groupCohomology.cocycles₁IsoOfIsTrivial
    (Rep.trivial ℤ H rationalModIntegers)).inv
      (characterRationalIntegers H
        (chi.comp H.subtype.toAdditive))
  change restriction (Rep.trivial ℤ G rationalModIntegers) H 1
      (groupCohomology.H1π (Rep.trivial ℤ G rationalModIntegers) cG) =
    groupCohomology.H1π (Rep.trivial ℤ H rationalModIntegers) cH
  have hmap := congrArg (fun f => f cG)
    (groupCohomology.H1π_comp_map H.subtype
      (𝟙 (Rep.trivial ℤ H rationalModIntegers)))
  simp only [ConcreteCategory.comp_apply] at hmap
  change groupCohomology.map H.subtype
      (𝟙 (Rep.trivial ℤ H rationalModIntegers)) 1
        (groupCohomology.H1π
          (Rep.trivial ℤ G rationalModIntegers) cG) = _
  rw [hmap]
  apply congrArg (groupCohomology.H1π
    (Rep.trivial ℤ H rationalModIntegers))
  apply groupCohomology.cocycles₁_ext
  intro h
  rfl

/-- Every rational character of a finite cyclic group is an integral
multiple of the character normalized at a chosen generator. -/
theorem rational_zsmul_generator
    {J : Type} [CommGroup J] [Finite J]
    (g : J) (hg : ∀ x : J, x ∈ Subgroup.zpowers g)
    (chi : RationalCharacter J) :
    ∃ j : ℤ, chi = j •
      multiplicativeRationalCharacter J g hg := by
  letI : Fintype J := Fintype.ofFinite J
  let n := Nat.card J
  let psi := multiplicativeRationalCharacter J g hg
  have hn : 0 < n := Nat.card_pos
  have htors : n • chi (Additive.ofMul g) = 0 := by
    calc
      n • chi (Additive.ofMul g) =
          chi (n • Additive.ofMul g) := (map_nsmul chi n _).symm
      _ = chi (Additive.ofMul (g ^ n)) := rfl
      _ = 0 := by rw [pow_card_eq_one']; exact map_zero chi
  obtain ⟨m, hm, hvalue⟩ :=
    (AddCircle.nsmul_eq_zero_iff (p := (1 : ℚ)) hn).mp htors
  let j : ℤ := m
  have hpsi : psi (Additive.ofMul g) =
      (((n : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) := by
    simp [psi, n, Nat.card_eq_fintype_card]
  have heval : chi (Additive.ofMul g) = j • psi (Additive.ofMul g) := by
    rw [hpsi]
    rw [← hvalue]
    rw [← AddCircle.coe_zsmul]
    congr 1
    simp [j, div_eq_mul_inv]
  refine ⟨j, ?_⟩
  apply AddMonoidHom.ext
  intro x
  obtain ⟨k, hk⟩ := hg x.toMul
  have hx : x = k • Additive.ofMul g := by
    apply Additive.toMul.injective
    simpa using hk.symm
  rw [hx, map_zsmul, heval]
  rw [map_zsmul]
  rfl

end

end Towers.CField.LRecip
