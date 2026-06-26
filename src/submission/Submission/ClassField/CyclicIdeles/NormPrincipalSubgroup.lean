import Submission.ClassField.CyclicIdeles.CyclicCohomology
import Submission.ClassField.CyclicIdeles.FiniteGalois

/-!
# Chapter VII, Section 5, Lemma 5.2

For a cyclic extension, the second inequality, vanishing of `H¹(G,C_L)`,
and the degree-two divisibility assertion are equivalent.  Moreover they are
equivalent to the displayed equality

`[I_K : Kˣ Nm(I_L)] = |H²(G,C_L)| = [L : K]`.

The last equality is deliberately included as an equivalent condition, not
as an unconditional conclusion: before one proves the second inequality,
Theorem 4.3 determines the ratio `|H²| / |H¹|`, so equality with the degree
holds exactly when any (hence all) of the three claims holds.
-/

namespace Submission.CField.CIdeles

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open Submission.CField.Shifting
open Submission.CField.Ideles
open Submission.CField.ICohomo
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

private abbrev CL
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Rep (ULift.{u} ℤ) Gal(L/K) :=
  ideleCohomologyRepresentation K L

private abbrev CLInt
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Rep ℤ Gal(L/K) :=
  classCokernelRepresentation (K := K) (L := L)

/-- Statement (a), the idèlic second inequality. -/
def ClaimA
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Prop :=
  Finite (IK K ⧸ normPrincipalSubgroup K L) ∧
    (normPrincipalSubgroup K L).index ∣ Module.finrank K L

/-- Statement (b), vanishing of degree-one idèle-class cohomology. -/
def ClaimB
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  IsZero (groupCohomology.H1 (CL K L))

/-- Statement (c), finiteness and degree-divisibility in degree two. -/
def ClaimC
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  Finite (groupCohomology.H2 (CL K L)) ∧
    Nat.card (groupCohomology.H2 (CL K L)) ∣ Module.finrank K L

/-- The separated claims are definitionally the three components bundled in
`Claims`. -/
theorem claims_principal_subgroup
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Claims K L ↔
      ClaimA K L ∧ ClaimB K L ∧ ClaimC K L :=
  Iff.rfl

/-- The parenthetical equality in Lemma 5.2, against the literal idèle
index and actual idèle-class cokernel representation. -/
def DegreeEquality
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  (normPrincipalSubgroup K L).index =
      Nat.card (groupCohomology.H2 (CL K L)) ∧
    Nat.card (groupCohomology.H2 (CL K L)) = Module.finrank K L

/-- A finite module is zero exactly when its underlying type has one
element. -/
private theorem zero_nat_card
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] [Finite M] :
    IsZero (ModuleCat.of R M) ↔ Nat.card M = 1 := by
  constructor
  · intro hzero
    exact Nat.card_eq_one_iff_unique.mpr
      ⟨ModuleCat.isZero_iff_subsingleton.mp hzero, inferInstance⟩
  · intro hcard
    letI : Subsingleton M := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact ModuleCat.isZero_of_subsingleton _

/-- Lemma 5.2 from Theorem 4.3, cyclic periodicity, and the one exact
comparison identifying Tate degree zero with the literal idèle index. -/
theorem normPrincipalStatement
    (h43 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
          letI : CommGroup Gal(L/K) := IsCyclic.commGroup
          HerbrandQuotientValue
            (classCokernelRepresentation (K := K) (L := L))
            (Module.finrank K L : ℚ)))
    (hindex : TateIndexBridge.{u})
    (hresize : ScalarResizingBridge.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          (ClaimA K L ↔ ClaimB K L) ∧
            (ClaimB K L ↔ ClaimC K L) ∧
            (ClaimA K L ↔ DegreeEquality K L)) := by
  intro K L _ _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let A : Rep ℤ Gal(L/K) := CLInt K L
  let B : Rep (ULift.{u} ℤ) Gal(L/K) := CL K L
  let n := Module.finrank K L
  have hnpos : 0 < n := Module.finrank_pos
  have hherbrand : HerbrandQuotientValue A (n : ℚ) := h43 K L
  letI : Finite (tateZero A) := hherbrand.1
  letI : Finite (tateNegOne A) := hherbrand.2.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  rcases hresize K L with ⟨⟨eNeg⟩, ⟨eZero⟩⟩
  let eOne := eNeg.trans
    (tateCohomologyNeg B g hg).toAddEquiv
  let eTwo := eZero.trans
    (tateCohomologyTwo B g hg).toAddEquiv
  letI : Finite (groupCohomology.H1 B) :=
    Finite.of_equiv (tateNegOne A) eOne.toEquiv
  letI : Finite (groupCohomology.H2 B) :=
    Finite.of_equiv (tateZero A) eTwo.toEquiv
  have hH1card : Nat.card (groupCohomology.H1 B) =
      Nat.card (tateNegOne A) :=
    (Nat.card_congr eOne.toEquiv).symm
  have hH2card : Nat.card (groupCohomology.H2 B) =
      Nat.card (tateZero A) :=
    (Nat.card_congr eTwo.toEquiv).symm
  have hindexH2 : (normPrincipalSubgroup K L).index =
      Nat.card (groupCohomology.H2 B) := by
    calc
      (normPrincipalSubgroup K L).index =
          Nat.card (tateZero A) := (hindex K L).symm
      _ = Nat.card (groupCohomology.H2 B) := hH2card.symm
  have hindexPos : 0 < (normPrincipalSubgroup K L).index := by
    rw [hindexH2]
    exact Nat.card_pos
  letI : Finite (IK K ⧸ normPrincipalSubgroup K L) :=
    Nat.finite_of_card_ne_zero <| by
      rw [← Subgroup.index_eq_card]
      exact hindexPos.ne'
  have htateProduct : Nat.card (tateZero A) =
      n * Nat.card (tateNegOne A) := by
    have hdenNe : (Nat.card (tateNegOne A) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hrat : (Nat.card (tateZero A) : ℚ) =
        (n : ℚ) * Nat.card (tateNegOne A) :=
      (div_eq_iff hdenNe).mp hherbrand.2.2
    exact_mod_cast hrat
  have hcardProduct : Nat.card (groupCohomology.H2 B) =
      n * Nat.card (groupCohomology.H1 B) := by
    calc
      Nat.card (groupCohomology.H2 B) =
          Nat.card (tateZero A) := hH2card
      _ = n * Nat.card (tateNegOne A) := htateProduct
      _ = n * Nat.card (groupCohomology.H1 B) := by rw [hH1card]
  have hBcard : ClaimB K L ↔
      Nat.card (groupCohomology.H1 B) = 1 := by
    exact zero_nat_card
      (R := ULift.{u} ℤ) (M := groupCohomology.H1 B)
  have hAtoB : ClaimA K L → ClaimB K L := by
    rintro ⟨_, hdiv⟩
    have hH2div : Nat.card (groupCohomology.H2 B) ∣ n := by
      rwa [hindexH2] at hdiv
    have hH2le : Nat.card (groupCohomology.H2 B) ≤ n :=
      Nat.le_of_dvd hnpos hH2div
    have hnleH2 : n ≤ Nat.card (groupCohomology.H2 B) := by
      rw [hcardProduct]
      exact Nat.le_mul_of_pos_right n Nat.card_pos
    have hH2eq : Nat.card (groupCohomology.H2 B) = n :=
      Nat.le_antisymm hH2le hnleH2
    apply hBcard.mpr
    apply Nat.eq_of_mul_eq_mul_left hnpos
    simpa only [mul_one, ← hcardProduct] using hH2eq
  have hBtoA : ClaimB K L → ClaimA K L := by
    intro hB
    have hH1eq : Nat.card (groupCohomology.H1 B) = 1 := hBcard.mp hB
    have hH2eq : Nat.card (groupCohomology.H2 B) = n := by
      rw [hcardProduct, hH1eq, mul_one]
    refine ⟨inferInstance, ?_⟩
    rw [hindexH2, hH2eq]
  have hAiffC : ClaimA K L ↔ ClaimC K L := by
    constructor
    · rintro ⟨_, hdiv⟩
      refine ⟨inferInstance, ?_⟩
      rwa [← hindexH2]
    · rintro ⟨_, hdiv⟩
      refine ⟨inferInstance, ?_⟩
      rwa [hindexH2]
  have hAiffB : ClaimA K L ↔ ClaimB K L :=
    ⟨hAtoB, hBtoA⟩
  refine ⟨hAiffB, ?_, ?_⟩
  · exact hAiffB.symm.trans hAiffC
  · constructor
    · intro hA
      have hB := hAtoB hA
      have hH1eq := hBcard.mp hB
      have hH2eq : Nat.card (groupCohomology.H2 B) = n := by
        rw [hcardProduct, hH1eq, mul_one]
      exact ⟨hindexH2, hH2eq⟩
    · rintro ⟨_, hH2eq⟩
      refine ⟨inferInstance, ?_⟩
      rw [hindexH2, hH2eq]

end

end Submission.CField.CIdeles
