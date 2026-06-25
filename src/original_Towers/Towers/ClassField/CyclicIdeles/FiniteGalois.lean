import Towers.ClassField.Shifting.GroupPeriodicityOdd
import Towers.ClassField.DirichletDensity.SecondInequality
import Towers.ClassField.NormIndex.HerbrandCardinalityBound
import Mathlib.Algebra.Module.ULift
import Mathlib.GroupTheory.PGroup

/-!
# Chapter VII, Section 5, Theorem 5.1

For every finite Galois extension `L/K`, with no commutativity hypothesis on
its Galois group, the second inequality and the two low-degree idèle-class
cohomology assertions hold simultaneously:

* `[I_K : Kˣ Nm(I_L)]` is finite and divides `[L : K]`;
* `H¹(G, C_L) = 0`;
* `H²(G, C_L)` is finite and its order divides `[L : K]`.

The idèle-class representation below is the literal cokernel of the
principal-idèle map constructed in Section 4.  The cyclic case is proved
from Theorem 4.3, cyclic periodicity, and the idealic second inequality of
VI.4.9.  The restriction/inflation induction of Lemmas 5.3 and 5.4 is kept
as one explicit reduction bridge; it assumes only the prime cyclic cases,
not any clause of the general theorem.
-/

namespace Towers.CField.CIdeles

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open Towers.CField.Shifting
open Towers.CField.RCGroups
open Towers.CField.ARecip
open Towers.CField.Ideles
open Towers.CField.DDensit
open Towers.CField.ICohomo
open Towers.CField.NIndex

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
    Rep ℤ Gal(L/K) :=
  classCokernelRepresentation (K := K) (L := L)

/-- Recover the additive Galois action carried by an integral
representation, without retaining its particular `ℤ`-module instance.  This
is used only to place the coefficient ring and Galois group in the common
universe required by Mathlib's ordinary group-cohomology API. -/
@[reducible]
private def additiveIntRepresentation
    {G : Type u} [Group G] (A : Rep.{u, 0, u} ℤ G) :
    DistribMulAction G A := by
  letI : Module ℤ A := A.hV2
  exact
    { smul := fun g x => A.ρ g x
      one_smul := fun x => by
        change A.ρ 1 x = x
        rw [map_one]
        rfl
      mul_smul := fun g h x => by
        change A.ρ (g * h) x = A.ρ g (A.ρ h x)
        rw [map_mul]
        rfl
      smul_zero := fun g => (A.ρ g).map_zero
      smul_add := fun g => (A.ρ g).map_add }

/-- The same additive action, regarded as linear over the universe lift of
`ℤ`.  Scalar multiplication by `r : ULift ℤ` is multiplication by `r.down`,
so no arithmetic data is changed. -/
private def uliftIntRepresentation
    {G M : Type u} [Group G] [AddCommGroup M]
    [DistribMulAction G M] : Representation (ULift.{u} ℤ) G M where
  toFun g :=
    { toFun := fun x => g • x
      map_add' := smul_add g
      map_smul' := fun r x =>
        (Representation.ofDistribMulAction ℤ G M g).map_smul r.down x }
  map_one' := by
    ext x
    exact one_smul _ _
  map_mul' g h := by
    ext x
    exact mul_smul _ _ _

/-- The actual idèle-class additive group and actual Galois action, with
`ℤ` replaced by its universe lift solely so that Mathlib can form ordinary
group cohomology when the number fields live in `Type u`. -/
noncomputable def ideleCohomologyRepresentation
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Rep (ULift.{u} ℤ) Gal(L/K) :=
  let A := CL K L
  let _ := additiveIntRepresentation A
  Rep.of (uliftIntRepresentation (G := Gal(L/K)) (M := A))

/-- The narrow scalar-resizing comparison missing from the library.  It
asserts only that replacing `ℤ` by `ULift ℤ`, while leaving the additive
group and Galois action unchanged, leaves the two exceptional Tate groups
unchanged up to additive equivalence.  It contains no finiteness,
vanishing, index, or divisibility conclusion. -/
def ScalarResizingBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    Nonempty
        (tateNegOne (CL K L) ≃+
          tateCohomologyOne
            (ideleCohomologyRepresentation K L)) ∧
      Nonempty
        (tateZero (CL K L) ≃+
          tateCohomologyZero
            (ideleCohomologyRepresentation K L))

/-- The three simultaneous conclusions of Theorem 5.1 for one actual
extension and its actual idèle-class representation. -/
def Claims
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Prop :=
  (Finite (IK K ⧸ normPrincipalSubgroup K L) ∧
      (normPrincipalSubgroup K L).index ∣ Module.finrank K L) ∧
    IsZero (groupCohomology.H1
      (ideleCohomologyRepresentation K L)) ∧
    (Finite (groupCohomology.H2
        (ideleCohomologyRepresentation K L)) ∧
      Nat.card (groupCohomology.H2
        (ideleCohomologyRepresentation K L)) ∣ Module.finrank K L)

/-- **Theorem VII.5.1, source statement.**  No cyclic, abelian, or solvable
hypothesis is imposed on `Gal(L/K)`. -/
def IdeleCohomologyClaims : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    Claims K L

/-- Package raw field types as the arbitrary finite number-field extension
used by the idealic statement of Theorem VI.4.9. -/
private def finiteExtensionTypes
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    NFExt K where
  carrier := L

/-- The exact Proposition V.4.6 translation needed to apply the idealic
Theorem VI.4.9: for a suitable modulus, its ray-ideal quotient has the same
index as the literal subgroup `Kˣ Nm(I_L)` of the idèles.

Only equality of the two displayed indices is recorded; no inequality or
cohomological conclusion is included. -/
def IdealIdeleBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L],
    ∃ m : Towers.CField.RCGroups.Modulus K,
      (normPrincipalSubgroup K L).index =
        (extensionRaySubgroup
          (finiteExtensionTypes K L) m).index

/-- The precise comparison required by the proof of Theorem 5.1.  Milne's
Proposition V.4.6 translation only needs the idèlic quotient to be no larger
than the ray-ideal quotient to transport the idealic second inequality.
Unlike the optional equality bridge above, this statement records exactly
that one required direction.  The quotient-finiteness argument is supplied
by Theorem VI.4.9; it is an explicit input here only because numerical
`Nat.card` monotonicity for a quotient map requires the source finite. -/
def IdealInequalityBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L],
    ∃ m : Towers.CField.RCGroups.Modulus K,
      Finite (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸
        extensionRaySubgroup (finiteExtensionTypes K L) m) →
        (normPrincipalSubgroup K L).index ≤
          (extensionRaySubgroup
            (finiteExtensionTypes K L) m).index

/-- The prime-cyclic cases which remain after Lemmas 5.3 and 5.4. -/
def PrimeCyclicCases : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    Nat.Prime (Module.finrank K L) → Claims K L

/-- The cases in which the Galois group is a `p`-group, for a specified
prime `p`. -/
def PGroupCases : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ), Nat.Prime p → IsPGroup p Gal(L/K) →
      Claims K L

/-- **Lemma VII.5.3, reduction bridge.**  Restriction to Sylow subgroups
reduces all three assertions to the `p`-group cases. -/
def SylowReductionBridge : Prop :=
  PGroupCases.{u} → IdeleCohomologyClaims.{u}

/-- **Lemma VII.5.4, reduction bridge.**  Inflation-restriction and
induction on the order of a `p`-group reduce its three assertions to cyclic
extensions of prime degree.

Both reduction bridges are one-way implications from explicitly supplied
smaller cases; neither assumes the general theorem. -/
def PReductionBridge : Prop :=
  PrimeCyclicCases.{u} → PGroupCases.{u}

/-- The idealic second inequality of VI.4.9 gives the upper bound for the
literal idèle index after the Proposition V.4.6 translation. -/
theorem idele_index_finrank
    (h49 : (∀ (K : Type u) [Field K] [NumberField K]
          (L : NFExt K) (m : Modulus K),
          IsGalois K L.carrier →
            Finite (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸
              extensionRaySubgroup L m) ∧
            (extensionRaySubgroup L m).index ≤
              Module.finrank K L.carrier))
    (htranslate : IdealInequalityBridge.{u})
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (normPrincipalSubgroup K L).index ≤ Module.finrank K L := by
  obtain ⟨m, hm⟩ := htranslate K L
  have h49m := h49 K (finiteExtensionTypes K L) m (by
    change IsGalois K L
    infer_instance)
  exact (hm h49m.1).trans h49m.2

/-- The cyclic case of Theorem 5.1.  The first inequality and VI.4.9 make
the idèle index equal to the degree.  Theorem 4.3 then makes Tate degree
minus one trivial; cyclic periodicity transports Tate degrees `-1` and `0`
to ordinary `H¹` and `H²`. -/
theorem claims_second_inequality
    (h43 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
          letI : CommGroup Gal(L/K) := IsCyclic.commGroup
          HerbrandQuotientValue
            (classCokernelRepresentation (K := K) (L := L))
            (Module.finrank K L : ℚ)))
    (hindex : TateIndexBridge.{u})
    (hresize : ScalarResizingBridge.{u})
    (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    (hsecond : (normPrincipalSubgroup K L).index ≤ Module.finrank K L) :
    Claims K L := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let A : Rep ℤ Gal(L/K) := CL K L
  let B : Rep (ULift.{u} ℤ) Gal(L/K) :=
    ideleCohomologyRepresentation K L
  have hherbrand : HerbrandQuotientValue A
      (Module.finrank K L : ℚ) := h43 K L
  letI : Finite (tateZero A) := hherbrand.1
  letI : Finite (tateNegOne A) := hherbrand.2.1
  have hzeroCardIndex : Nat.card (tateZero A) =
      (normPrincipalSubgroup K L).index := hindex K L
  have hdegreeLeIndex : Module.finrank K L ≤
      (normPrincipalSubgroup K L).index := by
    rw [← hzeroCardIndex]
    exact nat_herbrand_value
      A (Module.finrank K L) hherbrand
  have hindexEq : (normPrincipalSubgroup K L).index =
      Module.finrank K L := Nat.le_antisymm hsecond hdegreeLeIndex
  have hzeroCard : Nat.card (tateZero A) =
      Module.finrank K L := hzeroCardIndex.trans hindexEq
  have hdegreeNe : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hnegCard : Nat.card (tateNegOne A) = 1 := by
    have hdenNe : (Nat.card (tateNegOne A) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hzeroProduct :
        (Nat.card (tateZero A) : ℚ) =
          (Module.finrank K L : ℚ) *
            Nat.card (tateNegOne A) :=
      (div_eq_iff hdenNe).mp hherbrand.2.2
    have hproduct :
        (Module.finrank K L : ℚ) =
          (Module.finrank K L : ℚ) *
            Nat.card (tateNegOne A) := by
      calc
        (Module.finrank K L : ℚ) =
            Nat.card (tateZero A) := by
          exact_mod_cast hzeroCard.symm
        _ = _ := hzeroProduct
    apply Nat.cast_injective (R := ℚ)
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hdegreeNe :
      (Module.finrank K L : ℚ) ≠ 0)
    simpa only [Nat.cast_one, mul_one] using hproduct.symm
  rcases hresize K L with ⟨⟨eNeg⟩, ⟨eZero⟩⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let eOne : tateNegOne A ≃+
      groupCohomology.H1 B :=
    eNeg.trans
      (tateCohomologyNeg B g hg).toAddEquiv
  let eTwo : tateZero A ≃+
      groupCohomology.H2 B :=
    eZero.trans
      (tateCohomologyTwo B g hg).toAddEquiv
  letI : Finite (groupCohomology.H1 B) :=
    Finite.of_equiv (tateNegOne A) eOne.toEquiv
  have hH1card : Nat.card (groupCohomology.H1 B) = 1 := by
    rw [← hnegCard]
    exact (Nat.card_congr eOne.toEquiv).symm
  haveI : Subsingleton (groupCohomology.H1 B) :=
    (Nat.card_eq_one_iff_unique.mp hH1card).1
  have hH1zero : IsZero (groupCohomology.H1 B) :=
    ModuleCat.isZero_of_subsingleton _
  letI : Finite (groupCohomology.H2 B) :=
    Finite.of_equiv (tateZero A) eTwo.toEquiv
  have hH2card : Nat.card (groupCohomology.H2 B) =
      Module.finrank K L := by
    rw [← hzeroCard]
    exact (Nat.card_congr eTwo.toEquiv).symm
  have hquotCard : Nat.card (IK K ⧸ normPrincipalSubgroup K L) =
      Module.finrank K L := by
    rw [← hindexEq, Subgroup.index_eq_card]
  letI : Finite (IK K ⧸ normPrincipalSubgroup K L) :=
    Nat.finite_of_card_ne_zero (by rw [hquotCard]; exact hdegreeNe)
  refine ⟨⟨inferInstance, hindexEq.dvd⟩, hH1zero, inferInstance, ?_⟩
  exact hH2card.dvd

/-- Theorem 5.1 from the analytic second inequality and the exact
restriction/inflation reduction of Lemmas 5.3–5.4. -/
theorem representation_previous_results
    (h49 : (∀ (K : Type u) [Field K] [NumberField K]
          (L : NFExt K) (m : Modulus K),
          IsGalois K L.carrier →
            Finite (IdealsPrimeTo (NumberField.RingOfIntegers K) K m.finiteSupport ⧸
              extensionRaySubgroup L m) ∧
            (extensionRaySubgroup L m).index ≤
              Module.finrank K L.carrier))
    (htranslate : IdealInequalityBridge.{u})
    (h43 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
          letI : CommGroup Gal(L/K) := IsCyclic.commGroup
          HerbrandQuotientValue
            (classCokernelRepresentation (K := K) (L := L))
            (Module.finrank K L : ℚ)))
    (hindex : TateIndexBridge.{u})
    (hresize : ScalarResizingBridge.{u})
    (hsylow : SylowReductionBridge.{u})
    (hpgroup : PReductionBridge.{u}) :
    IdeleCohomologyClaims.{u} := by
  apply hsylow
  apply hpgroup
  intro K L _ _ _ _ _ _ _ _ hprime
  exact claims_second_inequality h43 hindex hresize K L
    (idele_index_finrank h49 htranslate K L)

end

end Towers.CField.CIdeles
