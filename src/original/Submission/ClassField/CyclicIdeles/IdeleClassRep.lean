import Mathlib.Data.Nat.Factorization.Basic
import Submission.ClassField.CohomologyOps.InjPrimaryComponent
import Submission.ClassField.Shifting.SylowDetection
import Submission.ClassField.CyclicIdeles.FiniteGalois

/-!
# Chapter VII, Section 5, Lemma 5.3

Theorem 5.1 reduces to the case of `p`-groups.  For a prime `p`, restrict the
actual idèle-class representation from `G = Gal(L/K)` to a Sylow `p`-subgroup
`P`.  Its fixed field is `E = L^P`, so the induction hypothesis applies to
the actual extension `L/E`.  Corollary II.1.33 makes restriction injective on
the `p`-primary component.

The positive-degree cardinal divisibility argument is proved below for an
arbitrary representation.  The remaining bridges are idèle-specific:

* comparison of the restricted idèle-class representation with the actual
  idèle-class representation over the fixed field;
* finiteness detection for `H²` from all Sylow restrictions;
* the analogous Tate-degree-zero statements, expressed directly for the
  actual idèle norm index.

None of these bridges assumes a general Theorem 5.1 conclusion.
-/

namespace Submission.CField.CIdeles

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open Submission.CField.COps
open Submission.CField.Shifting
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

/-- The actual fixed field of a Sylow subgroup. -/
private abbrev sylowFixedField
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (p : ℕ) (P : Sylow p Gal(L/K)) :=
  IntermediateField.fixedField (P : Subgroup Gal(L/K))

/-- The missing arithmetic comparison at one actual Sylow fixed field.
The fields identify its `H¹` and `H²` with restriction of the literal
idèle-class cokernel for `L/K`.  The Galois structure on `L/L^P` is the
canonical fixed-field instance. -/
structure SylowFixedData
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)) where
  h_1_equiv :
    groupCohomology.H1 (ideleClassRep (sylowFixedField K L p P) L) ≃+
      groupCohomology.H1
        (Rep.res (P : Subgroup Gal(L/K)).subtype (ideleClassRep K L))
  h_2_equiv :
    groupCohomology.H2 (ideleClassRep (sylowFixedField K L p P) L) ≃+
      groupCohomology.H2
        (Rep.res (P : Subgroup Gal(L/K)).subtype (ideleClassRep K L))

/-- Fixed-field comparison for every Sylow subgroup. -/
def SylowFixedBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)),
    Nonempty (SylowFixedData K L p P)

/-- The exact finite-cardinality consequence not packaged by the current
positive-cohomology API: if every Sylow restriction of `H²` is finite, then
the ambient `H²` is finite.  Restriction injectivity itself is already
available as Corollary II.1.33 and is used below for divisibility. -/
def HFinitenessBridge : Prop :=
  ∀ {G : Type u} [Group G] [Finite G]
    (A : Rep (ULift.{u} ℤ) G),
    (∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Finite (groupCohomology.H2
        (Rep.res (P : Subgroup G).subtype A))) →
    Finite (groupCohomology.H2 A)

/-- Finiteness of the literal idèle norm quotient is detected on all Sylow
fixed fields.  This is the finiteness half of the Tate-degree-zero transfer. -/
def IdeleFinitenessBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    (∀ (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)),
      Finite (IK (sylowFixedField K L p P) ⧸
        normPrincipalSubgroup (sylowFixedField K L p P) L)) →
    Finite (IK K ⧸ normPrincipalSubgroup K L)

/-- The pointwise `p`-primary index comparison at one Sylow subgroup. -/
structure IdelePrimaryData
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)) : Prop where
  ordProj_dvd :
    Finite (IK K ⧸ normPrincipalSubgroup K L) →
    (normPrincipalSubgroup (sylowFixedField K L p P) L).index ∣
      Nat.card P →
    ordProj[p] (normPrincipalSubgroup K L).index ∣ Nat.card P

/-- The `p`-part of the ambient idèle norm index injects into the index over
the Sylow fixed field.  The hypothesis is precisely the divisibility supplied
by the `p`-group case.  The pointwise data wrapper keeps the nested quotient
type opaque while the universal bridge is introduced. -/
structure IdelePrimaryBridge : Prop where
  data :
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)),
      IdelePrimaryData K L p P

/-- If the `p`-primary part of `n` is bounded by a Sylow `p`-subgroup for
every prime, then `n` divides the order of the finite group. -/
private theorem ord_proj_sylow
    {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : n ≠ 0)
    (hprimary : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      ordProj[p] n ∣ Nat.card P) :
    n ∣ Nat.card G := by
  apply (Nat.factorization_prime_le_iff_dvd hn Nat.card_pos.ne').mp
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p G := Classical.choice Sylow.nonempty
  have hpow : p ^ n.factorization p ∣
      p ^ (Nat.card G).factorization p := by
    rw [← P.card_eq_multiplicity]
    exact hprimary p P
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpow

/-- Corollary II.1.33 gives the full cardinal divisibility in positive
degree once finiteness is known and every Sylow restriction has cardinal
dividing the order of that Sylow subgroup. -/
theorem cohomology_dvd_sylow
    {G : Type u} [Group G] [Finite G]
    (A : Rep (ULift.{u} ℤ) G) (r : ℕ)
    [Finite (groupCohomology A r)]
    (hSylow : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G),
      Finite (groupCohomology (Rep.res (P : Subgroup G).subtype A) r) ∧
      Nat.card (groupCohomology (Rep.res (P : Subgroup G).subtype A) r) ∣
        Nat.card P) :
    Nat.card (groupCohomology A r) ∣ Nat.card G := by
  apply ord_proj_sylow
    (Nat.card (groupCohomology A r)) Nat.card_pos.ne'
  intro p _ P
  let T := groupCohomology (Rep.res (P : Subgroup G).subtype A) r
  letI : Finite T := (hSylow p P).1
  let M := Multiplicative (groupCohomology A r)
  let Q : Sylow p M := Classical.choice Sylow.nonempty
  let f : Q →* Multiplicative T :=
    (restriction A (P : Subgroup G) r).hom.toAddMonoidHom.toMultiplicative.comp
      (Q : Subgroup M).subtype
  have hQprimary (x : Q) :
      Multiplicative.toAdd (x : M) ∈
        AddCommGroup.primaryComponent (groupCohomology A r) p := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') x
    rw [AddCommGroup.mem_primaryComponent]
    refine ⟨k, ?_⟩
    change Multiplicative.toAdd ((x : M) ^ (p ^ k)) =
      Multiplicative.toAdd 1
    apply Multiplicative.toAdd.injective
    rw [← hk, ← orderOf_submonoid]
    exact pow_orderOf_eq_one (x : M)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    change Multiplicative.toAdd (x : M) = Multiplicative.toAdd (y : M)
    apply restriction_inj_component A p P r
      (hQprimary x) (hQprimary y)
    exact hxy
  have hQrange : Nat.card Q = Nat.card f.range :=
    Nat.card_congr (Equiv.ofInjective f hf)
  have hQdvdT : Nat.card Q ∣ Nat.card T := by
    rw [hQrange]
    exact f.range.card_subgroup_dvd_card
  have hQdvdP : Nat.card Q ∣ Nat.card P :=
    hQdvdT.trans (hSylow p P).2
  rw [Q.card_eq_multiplicity] at hQdvdP
  exact hQdvdP

/-- **Lemma VII.5.3, source reduction.**  If Theorem 5.1 is known for every
finite Galois extension whose Galois group is a `p`-group, then all three
claims hold for every finite Galois extension. -/
theorem sylow_reduction
    (hpGroups : PGroupCases.{u})
    (hfixed : SylowFixedBridge.{u})
    (hH2finite : HFinitenessBridge.{u})
    (hindexFinite : IdeleFinitenessBridge.{u})
    (hindexPrimary : IdelePrimaryBridge.{u}) :
    IdeleCohomologyClaims.{u} := by
  intro K L _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  let A : Rep (ULift.{u} ℤ) Gal(L/K) := ideleClassRep K L
  have sylowClaims (p : ℕ) [Fact p.Prime] (P : Sylow p Gal(L/K)) :
      let E := sylowFixedField K L p P
      Claims E L := by
    dsimp only
    have hpGal : IsPGroup p Gal(L/sylowFixedField K L p P) :=
      IsPGroup.of_equiv P.isPGroup'
        (IntermediateField.subgroupEquivAlgEquiv (P : Subgroup Gal(L/K)))
    exact hpGroups (sylowFixedField K L p P) L p Fact.out hpGal
  have hH1zero : IsZero (groupCohomology.H1 A) := by
    letI : Subsingleton (groupCohomology.H1 A) :=
      subsingleton_group_sylow A 1 fun p _ P => by
        let data := Classical.choice (hfixed K L p P)
        letI : Subsingleton (groupCohomology.H1
            (ideleClassRep (sylowFixedField K L p P) L)) :=
          ModuleCat.subsingleton_of_isZero (sylowClaims p P).2.1
        exact data.h_1_equiv.symm.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hindexFin : Finite (IK K ⧸ normPrincipalSubgroup K L) := by
    apply hindexFinite K L
    intro p _ P
    exact (sylowClaims p P).1.1
  letI : Finite (IK K ⧸ normPrincipalSubgroup K L) := hindexFin
  have hindexDvd : (normPrincipalSubgroup K L).index ∣
      Module.finrank K L := by
    rw [← IsGalois.card_aut_eq_finrank]
    apply ord_proj_sylow
      (normPrincipalSubgroup K L).index
    · rw [Subgroup.index_eq_card]
      exact Nat.card_pos.ne'
    · intro p _ P
      apply (hindexPrimary.data K L p P).ordProj_dvd inferInstance
      rw [← IntermediateField.finrank_fixedField_eq_card]
      exact (sylowClaims p P).1.2
  have hH2Fin : Finite (groupCohomology.H2 A) := by
    apply hH2finite A
    intro p _ P
    let data := Classical.choice (hfixed K L p P)
    apply Nat.finite_of_card_ne_zero
    rw [(Nat.card_congr data.h_2_equiv.toEquiv).symm]
    letI : Finite (groupCohomology.H2
        (ideleClassRep (sylowFixedField K L p P) L)) :=
      (sylowClaims p P).2.2.1
    exact Nat.card_pos.ne'
  letI : Finite (groupCohomology.H2 A) := hH2Fin
  have hH2Dvd : Nat.card (groupCohomology.H2 A) ∣
      Module.finrank K L := by
    rw [← IsGalois.card_aut_eq_finrank]
    apply cohomology_dvd_sylow A 2
    intro p _ P
    let data := Classical.choice (hfixed K L p P)
    have hfixedFinite : Finite (groupCohomology.H2
        (ideleClassRep (sylowFixedField K L p P) L)) :=
      (sylowClaims p P).2.2.1
    have hrestrictedFinite : Finite (groupCohomology.H2
        (Rep.res (P : Subgroup Gal(L/K)).subtype A)) := by
      apply Nat.finite_of_card_ne_zero
      rw [(Nat.card_congr data.h_2_equiv.toEquiv).symm]
      letI := hfixedFinite
      exact Nat.card_pos.ne'
    refine ⟨hrestrictedFinite, ?_⟩
    rw [(Nat.card_congr data.h_2_equiv.toEquiv).symm,
      ← IntermediateField.finrank_fixedField_eq_card]
    exact (sylowClaims p P).2.2.2
  exact ⟨⟨hindexFin, hindexDvd⟩, hH1zero, hH2Fin, hH2Dvd⟩

/-- Lemma 5.3 supplies the formerly abstract Sylow reduction interface used
in `IdeleCohomologyClaims`. -/
theorem sylow_bridge_index
    (hfixed : SylowFixedBridge.{u})
    (hH2finite : HFinitenessBridge.{u})
    (hindexFinite : IdeleFinitenessBridge.{u})
    (hindexPrimary : IdelePrimaryBridge.{u}) :
    SylowReductionBridge.{u} := by
  intro hpGroups
  exact sylow_reduction hpGroups hfixed hH2finite
    hindexFinite hindexPrimary

end

end Submission.CField.CIdeles
