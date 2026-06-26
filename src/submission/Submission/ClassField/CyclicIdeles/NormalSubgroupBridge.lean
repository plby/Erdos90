import Submission.ClassField.LocalClass.InflationRestriction
import Submission.ClassField.CyclicIdeles.FiniteGalois

/-!
# Chapter VII, Section 5, Lemma 5.4

Theorem 5.1 for `p`-groups reduces, by induction on their order, to cyclic
extensions of prime degree.  For a nontrivial `p`-group `G`, choose a normal
subgroup `H` of index `p` and put `E = L^H`.  The two smaller extensions are
`E/K`, cyclic of degree `p`, and `L/E`, with Galois group `H`.

This file uses the actual idèle-class representations and the full
inflation--restriction complexes of Proposition II.1.34.  Only the arithmetic
comparisons between those abstract restriction/invariant representations and
the literal idèle-class groups of the two fixed-field extensions are isolated
as interfaces.
-/

namespace Submission.CField.CIdeles

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open Submission.CField.COps
open Submission.CField.Shifting
open Submission.CField.LClass
open Submission.CField.Ideles
open Submission.CField.NIndex

noncomputable section

universe u

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (NumberField.RingOfIntegers K) K

private abbrev normPrincipalSubgroup
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Subgroup (IK K) :=
  principalIdeles (NumberField.RingOfIntegers K) K ⊔
    ideleNormSubgroup (K := K) (L := L)

private abbrev ideleClassRep
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Rep (ULift.{u} ℤ) Gal(L/K) :=
  ideleCohomologyRepresentation K L

private abbrev fixedField
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (H : Subgroup Gal(L/K)) :=
  IntermediateField.fixedField H

/-- The elementary group-theoretic input GT 4.17: a nontrivial finite
`p`-group contains a normal subgroup of index `p`.  No class-field-theoretic
conclusion occurs in this interface. -/
def NormalSubgroupBridge : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (G : Type u) [Group G] [Finite G],
      IsPGroup p G → Nat.card G ≠ 1 →
        ∃ H : Subgroup G, H.Normal ∧ H.index = p

/-- The order-one base of the induction.  This contains only the trivial
extension case, not a proper or general `p`-group case. -/
def TrivialExtensionBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    Module.finrank K L = 1 → Claims K L

/-- Comparison data at the actual fixed field `E = L^H`.

The four cohomological fields are precisely the identifications

* `C_L^H = C_E`, with the quotient action of `G/H`, and
* the restriction of `C_L` to `H` with the idèle-class representation for
  `L/E`.

The degree field is the standard fixed-field identity `[E:K] = (G:H)`.
No vanishing, finiteness, or divisibility assertion is assumed here. -/
structure FixedFieldData
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] where
  isGalois_top : IsGalois (fixedField K L H) L
  degree_base_index : Module.finrank K (fixedField K L H) = H.index
  h_1_fixed :
    letI : IsGalois (fixedField K L H) L := isGalois_top
    IsZero (groupCohomology.H1 (ideleClassRep K (fixedField K L H))) →
      IsZero (groupCohomology.H1
        ((ideleClassRep K L).quotientToInvariants H))
  restricted_h_1 :
    letI : IsGalois (fixedField K L H) L := isGalois_top
    IsZero (groupCohomology.H1 (ideleClassRep (fixedField K L H) L)) →
      IsZero (groupCohomology.H1
        (Rep.res H.subtype (ideleClassRep K L)))
  card_fixed_field :
    letI : IsGalois (fixedField K L H) L := isGalois_top
    Nat.card (groupCohomology.H2
        ((ideleClassRep K L).quotientToInvariants H)) =
      Nat.card (groupCohomology.H2
        (ideleClassRep K (fixedField K L H)))
  restricted_card_field :
    letI : IsGalois (fixedField K L H) L := isGalois_top
    Nat.card (groupCohomology.H2
        (Rep.res H.subtype (ideleClassRep K L))) =
      Nat.card (groupCohomology.H2
        (ideleClassRep (fixedField K L H) L))

/-- The fixed-field comparison above, for every normal subgroup. -/
def FixedFieldBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal],
    Nonempty (FixedFieldData K L H)

/-- The exact norm-index consequence of the surjection in the printed proof:
the norm index for `L/K` divides the product of the two norm indices in the
tower `L/E/K`.  This bridge contains no degree bound. -/
def IndexTowerBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal],
    let E := fixedField K L H
    (normPrincipalSubgroup K L).index ∣
      (normPrincipalSubgroup K E).index *
        (normPrincipalSubgroup E L).index

/-- A middle additive group in a finite exact segment is finite when both
neighbors are finite. -/
theorem finite_middle_exact
    {A : Type u} {B : Type u} {C : Type u}
    [AddGroup A] [AddGroup B] [AddGroup C]
    [Finite A] [Finite C]
    (f : A →+ B) (g : B →+ C) (hfg : Function.Exact f g) :
    Finite B := by
  classical
  let s : C → B := fun c =>
    if hc : ∃ b, g b = c then Classical.choose hc else 0
  have hs (b : B) : g (s (g b)) = g b := by
    simp only [s]
    rw [dif_pos ⟨b, rfl⟩]
    exact (Classical.choose_spec (show ∃ b', g b' = g b from ⟨b, rfl⟩))
  apply Finite.of_surjective (fun ac : A × C => f ac.1 + s ac.2)
  intro b
  have hmem : b - s (g b) ∈ Set.range f := by
    apply (hfg _).mp
    rw [map_sub, hs, sub_self]
  obtain ⟨a, ha⟩ := hmem
  refine ⟨(a, g b), ?_⟩
  change f a + s (g b) = b
  rw [ha]
  exact sub_add_cancel b (s (g b))

/-- Divisibility, rather than only an inequality, for a finite exact segment
`0 → A → B → C`. -/
theorem middle_dvd_exact
    {A : Type u} {B : Type u} {C : Type u}
    [AddGroup A] [AddGroup B] [AddGroup C]
    [Finite A] [Finite B] [Finite C]
    (f : A →+ B) (g : B →+ C) (hf : Function.Injective f)
    (hfg : Function.Exact f g) :
    Nat.card B ∣ Nat.card A * Nat.card C := by
  have hcardQ := congrArg (fun q : ℚˣ ↦ (q : ℚ))
    (card_range_mul f g hfg)
  have hcard : Nat.card B = Nat.card f.range * Nat.card g.range := by
    have hcardQ' : (Nat.card B : ℚ) =
        (Nat.card f.range : ℚ) * Nat.card g.range := by
      simpa only [card_unit_val, Units.val_mul, Nat.cast_mul]
        using hcardQ
    exact_mod_cast hcardQ'
  have hfcard : Nat.card f.range = Nat.card A := by
    symm
    exact Nat.card_congr (Equiv.ofInjective f hf)
  rw [hcard, hfcard]
  exact Nat.mul_dvd_mul_left _ (AddSubgroup.card_addSubgroup_dvd_card g.range)

/-- The degree-two inflation--restriction exact sequence gives the order
divisibility used in Lemma 5.4. -/
theorem nat_cohomology_1
    {G : Type u} [Group G] (A : Rep (ULift.{u} ℤ) G)
    (H : Subgroup G) [H.Normal]
    (hH1 : IsZero (groupCohomology.H1 (Rep.res H.subtype A)))
    [Finite (groupCohomology.H2 (A.quotientToInvariants H))]
    [Finite (groupCohomology.H2 A)]
    [Finite (groupCohomology.H2 (Rep.res H.subtype A))] :
    Nat.card (groupCohomology.H2 A) ∣
      Nat.card (groupCohomology.H2 (A.quotientToInvariants H)) *
        Nat.card (groupCohomology.H2 (Rep.res H.subtype A)) := by
  let hvanish : ∀ j : ℕ, 0 < j → j < 2 →
      IsZero (groupCohomology (Rep.res H.subtype A) j) := by
    intro j hj hj2
    interval_cases j
    exact hH1
  let X := restrictionCochainsComplex A H 2 (by omega) hvanish
  have hmono : Mono X.f :=
    inflation_mono A H 2 (by omega) hvanish
  have hexact : Function.Exact X.f X.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact X).mp <| by
      exact restrictionCochainsShort A H 2 (by omega) hvanish
  exact middle_dvd_exact
    X.f.hom.toAddMonoidHom X.g.hom.toAddMonoidHom
    ((ModuleCat.mono_iff_injective X.f).mp hmono) hexact

/-- The same degree-two inflation--restriction segment also supplies
finiteness of the middle cohomology group from finiteness of its neighbors. -/
theorem cohomology_two_1
    {G : Type u} [Group G] (A : Rep (ULift.{u} ℤ) G)
    (H : Subgroup G) [H.Normal]
    (hH1 : IsZero (groupCohomology.H1 (Rep.res H.subtype A)))
    [Finite (groupCohomology.H2 (A.quotientToInvariants H))]
    [Finite (groupCohomology.H2 (Rep.res H.subtype A))] :
    Finite (groupCohomology.H2 A) := by
  let hvanish : ∀ j : ℕ, 0 < j → j < 2 →
      IsZero (groupCohomology (Rep.res H.subtype A) j) := by
    intro j hj hj2
    interval_cases j
    exact hH1
  let X := restrictionCochainsComplex A H 2 (by omega) hvanish
  have hexact : Function.Exact X.f X.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact X).mp <| by
      exact restrictionCochainsShort A H 2 (by omega) hvanish
  letI : Finite X.X₁ := by
    dsimp only [X, restrictionCochainsComplex]
    infer_instance
  letI : Finite X.X₃ := by
    dsimp only [X, restrictionCochainsComplex]
    infer_instance
  exact finite_middle_exact
    X.f.hom.toAddMonoidHom X.g.hom.toAddMonoidHom hexact

set_option maxHeartbeats 1000000 in
-- Fixed-field and cohomology instance synthesis makes this proof expensive.
/-- The induction in Lemma 5.4, using the literal fixed field and the actual
inflation--restriction complexes.  The nested fixed-field and cohomology
elaboration is instance-heavy. -/
theorem pGroup_reduction
    (hprime : PrimeCyclicCases.{u})
    (hnormal : NormalSubgroupBridge.{u})
    (htrivial : TrivialExtensionBridge.{u})
    (hfixed : FixedFieldBridge.{u})
    (hnorm : IndexTowerBridge.{u}) :
    PGroupCases.{u} := by
  intro K L _ _ _ _ _ _ _ p hp hpGroup
  letI : Fact p.Prime := ⟨hp⟩
  generalize hn : Nat.card Gal(L/K) = n
  induction n using Nat.strong_induction_on generalizing K L with
  | h n ih =>
      by_cases hdegree : Module.finrank K L = 1
      · exact htrivial K L hdegree
      · have hcardNe : Nat.card Gal(L/K) ≠ 1 := by
          rw [IsGalois.card_aut_eq_finrank]
          exact hdegree
        obtain ⟨H, hHnormal, hHindex⟩ :=
          hnormal p hp Gal(L/K) hpGroup hcardNe
        letI : H.Normal := hHnormal
        let E := fixedField K L H
        let data := Classical.choice (hfixed K L H)
        letI : IsGalois E L := data.isGalois_top
        letI : IsGalois K E := IsGalois.of_fixedField_normal_subgroup H
        have hEdegree : Module.finrank K E = p :=
          data.degree_base_index.trans hHindex
        letI : IsCyclic Gal(E/K) := by
          apply isCyclic_of_prime_card (p := p)
          rw [IsGalois.card_aut_eq_finrank, hEdegree]
        have hbase : Claims K E :=
          hprime K E (hEdegree ▸ hp)
        have hHcardLt : Nat.card H < Nat.card Gal(L/K) := by
          have hcardMul : Nat.card H * p = Nat.card Gal(L/K) := by
            rw [← hHindex]
            exact H.card_mul_index
          rw [← hcardMul]
          exact lt_mul_of_one_lt_right Nat.card_pos hp.one_lt
        have htopDegree : Module.finrank E L = Nat.card H :=
          IntermediateField.finrank_fixedField_eq_card H
        have hpTop : IsPGroup p Gal(L/E) :=
          IsPGroup.of_equiv (hpGroup.to_subgroup H)
            (IntermediateField.subgroupEquivAlgEquiv H)
        have htop : Claims E L := by
          apply ih (Nat.card Gal(L/E))
          · rw [IsGalois.card_aut_eq_finrank, htopDegree]
            exact hHcardLt.trans_eq hn
          · exact hpTop
          · rw [IsGalois.card_aut_eq_finrank, htopDegree]
        let A : Rep (ULift.{u} ℤ) Gal(L/K) := ideleClassRep K L
        have hrestrictedH1 : IsZero
            (groupCohomology.H1 (Rep.res H.subtype A)) :=
          data.restricted_h_1 htop.2.1
        have hquotientH1 : IsZero
            (groupCohomology.H1 (A.quotientToInvariants H)) :=
          data.h_1_fixed hbase.2.1
        have hH1 : IsZero (groupCohomology.H1 A) := by
          let hnone : ∀ j : ℕ, 0 < j → j < 1 →
              IsZero (groupCohomology (Rep.res H.subtype A) j) := by
            omega
          let X := restrictionCochainsComplex A H 1 (by omega) hnone
          have hexact : X.Exact := restrictionCochainsShort A H 1 (by omega) hnone
          apply hexact.isZero_X₂
          · exact hquotientH1.eq_of_src _ _
          · exact hrestrictedH1.eq_of_tgt _ _
        have hquotientH2Finite : Finite
            (groupCohomology.H2 (A.quotientToInvariants H)) := by
          apply Nat.finite_of_card_ne_zero
          rw [data.card_fixed_field]
          letI : Finite (groupCohomology.H2 (ideleClassRep K E)) :=
            hbase.2.2.1
          exact Nat.card_pos.ne'
        have hrestrictedH2Finite : Finite
            (groupCohomology.H2 (Rep.res H.subtype A)) := by
          apply Nat.finite_of_card_ne_zero
          rw [data.restricted_card_field]
          letI : Finite (groupCohomology.H2 (ideleClassRep E L)) :=
            htop.2.2.1
          exact Nat.card_pos.ne'
        letI : Finite (groupCohomology.H2 (A.quotientToInvariants H)) :=
          hquotientH2Finite
        letI : Finite (groupCohomology.H2 (Rep.res H.subtype A)) :=
          hrestrictedH2Finite
        have hH2Finite : Finite (groupCohomology.H2 A) :=
          cohomology_two_1 A H hrestrictedH1
        letI : Finite (groupCohomology.H2 A) := hH2Finite
        have hH2DvdProduct : Nat.card (groupCohomology.H2 A) ∣
            Nat.card (groupCohomology.H2 (A.quotientToInvariants H)) *
              Nat.card (groupCohomology.H2 (Rep.res H.subtype A)) :=
          nat_cohomology_1 A H hrestrictedH1
        have hH2DvdDegree : Nat.card (groupCohomology.H2 A) ∣
            Module.finrank K L := by
          apply hH2DvdProduct.trans
          rw [data.card_fixed_field,
            data.restricted_card_field,
            ← Module.finrank_mul_finrank K E L]
          exact Nat.mul_dvd_mul hbase.2.2.2 htop.2.2.2
        have hindexDvdProduct : (normPrincipalSubgroup K L).index ∣
            (normPrincipalSubgroup K E).index *
              (normPrincipalSubgroup E L).index := by
          exact hnorm K L H
        have hindexDvdDegree : (normPrincipalSubgroup K L).index ∣
            Module.finrank K L := by
          apply hindexDvdProduct.trans
          rw [← Module.finrank_mul_finrank K E L]
          exact Nat.mul_dvd_mul hbase.1.2 htop.1.2
        have hindexPos : 0 < (normPrincipalSubgroup K L).index :=
          Nat.pos_of_dvd_of_pos hindexDvdDegree Module.finrank_pos
        have hindexFinite : Finite
            (IK K ⧸ normPrincipalSubgroup K L) := by
          apply Nat.finite_of_card_ne_zero
          rw [← Subgroup.index_eq_card]
          exact hindexPos.ne'
        exact ⟨⟨hindexFinite, hindexDvdDegree⟩, hH1,
          hH2Finite, hH2DvdDegree⟩

/-- Lemma 5.4 supplies the formerly abstract `p`-group reduction interface
used by Theorem 5.1. -/
theorem p_reduction_bridge
    (hnormal : NormalSubgroupBridge.{u})
    (htrivial : TrivialExtensionBridge.{u})
    (hfixed : FixedFieldBridge.{u})
    (hnorm : IndexTowerBridge.{u}) :
    (PReductionBridge.{u}) := by
  intro hprime
  exact pGroup_reduction hprime hnormal htrivial hfixed hnorm

end

end Submission.CField.CIdeles
