import Submission.ClassField.IdeleCohomology.NormInvariants
import Submission.ClassField.HerbrandQuotients.FiniteAbovePlaces
import Submission.ClassField.NormIndex.FractionalIdealPrime

/-!
# Chapter VII, Section 4, Theorem 4.3

For a finite cyclic extension `L/K`, the Herbrand quotient of the idèle
class group is `[L : K]`.

The representations in this file are literal.  The idèle-class
representation is the cokernel of the diagonal map `Lˣ → I_L`, and the
restricted quotient used in Milne's proof is the cokernel of the restricted
diagonal `U(T) → I_{L,T}`.  Thus the remaining bridges below do not replace
the idèle class group by an abstract module: they record precisely the
quotient comparison and Herbrand-quotient multiplicativity used in the
source proof.
-/

namespace Submission.CField.NIndex

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open scoped BigOperators
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HQuotie

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The diagonal embedding of the actual `T`-unit group into the actual
restricted idèle group `I_{L,T}`. -/
noncomputable def unitsPlacesIdeles
    (S : Finset (NumberFieldPlace K)) :
    unitsAtPlaces (K := K) (L := L) S →*
      ICohomo.idelesAtPlaces (K := K) (L := L) S where
  toFun x :=
    ⟨principalIdele (NumberField.RingOfIntegers L) L (x : Lˣ),
      (principal_ideles_places
        (K := K) (L := L) S (x : Lˣ)).2 x.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (principalIdele (NumberField.RingOfIntegers L) L)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (principalIdele (NumberField.RingOfIntegers L) L)
      (x : Lˣ) (y : Lˣ)

/-- The equivariant restricted diagonal `U(T) → I_{L,T}`. -/
noncomputable def restrictedPrincipalHom
    (S : Finset (NumberFieldPlace K)) :
    unitsPlacesRepresentation (K := K) (L := L) S ⟶
      idelesRepresentation (K := K) (L := L) S := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  letI := idelesGaloisAction (K := K) (L := L)
  letI := placesDistribAction (K := K) (L := L) S
  letI := idelesDistribAction (K := K) (L := L) S
  exact Rep.ofHom
    { toLinearMap :=
        (MonoidHom.toAdditive
          (unitsPlacesIdeles (K := K) (L := L) S)).toIntLinearMap
      isIntertwining' := fun sigma ↦ by
        apply LinearMap.ext
        intro x
        apply Additive.toMul.injective
        simp only [Representation.ofMulDistribMulAction_apply_apply,
          AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
          LinearMap.coe_comp, Function.comp_apply, toMul_ofMul]
        apply Subtype.ext
        change
          (((unitsPlacesIdeles (K := K) (L := L) S)
            ((placesDistribAction (K := K) (L := L) S).smul sigma x.toMul) :
              ICohomo.idelesAtPlaces (K := K) (L := L) S) :
            IdeleGroup (NumberField.RingOfIntegers L) L) =
          (((idelesDistribAction (K := K) (L := L) S).smul sigma
            ((unitsPlacesIdeles (K := K) (L := L) S) x.toMul) :
              ICohomo.idelesAtPlaces (K := K) (L := L) S) :
            IdeleGroup (NumberField.RingOfIntegers L) L)
        simpa [unitsPlacesIdeles, idelesDistribAction, concreteActionData,
          idelesGaloisAction] using (IAData.smul_principalIdele
          (concreteActionData (K := K) (L := L))
          sigma (x.toMul : Lˣ)).symm }

/-- The literal quotient `I_{L,T}/U(T)` occurring in the proof. -/
abbrev restrictedIdeleRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep ℤ Gal(L/K) :=
  cokernel (restrictedPrincipalHom (K := K) (L := L) S)

/-- The literal idèle-class representation `C_L = I_L/Lˣ`, formed from
the concrete Galois action on idèles. -/
abbrev classCokernelRepresentation : Rep ℤ Gal(L/K) :=
  cokernel
    (concreteActionData (K := K) (L := L)).principalIdeleHom

/-- Condition (b) on the set chosen in Milne's proof: every ramified finite
prime lies above a member of `S`. -/
def ContainsRamifiedPlaces
    (S : Finset (NumberFieldPlace K)) : Prop :=
  ∀ Q : FinitePrime L,
    Ideal.ramificationIdx
        (Q.under (NumberField.RingOfIntegers K)).asIdeal Q.asIdeal ≠ 1 →
      (Sum.inl (Q.under (NumberField.RingOfIntegers K)) : NumberFieldPlace K) ∈ S

/-- Condition (c) exactly as it appears in the source: `S` contains the
contractions to `K` of finite primes whose classes generate the ideal class
group of `L`.  The auxiliary finset may also contain infinite places, which
do not affect `CIGenera`. -/
def ContainsContractionsGenerators
    (S : Finset (NumberFieldPlace K)) : Prop :=
  ∃ T : Finset (NumberFieldPlace L),
    CIGenera L T ∧
      ∀ Q : FinitePrime L,
        (Sum.inl Q : NumberFieldPlace L) ∈ T →
          (Sum.inl (Q.under (NumberField.RingOfIntegers K)) : NumberFieldPlace K) ∈ S

/-- The exact consequence of condition (c) used in the proof: the chosen
restricted idèles together with principal idèles generate all idèles.  By
Lemma 4.2 this follows after `S` contains the contractions of finite-prime
generators of the ideal class group of `L`. -/
def GeneratesIdelesPrincipal
    (S : Finset (NumberFieldPlace K)) : Prop :=
  principalIdeles (NumberField.RingOfIntegers L) L ⊔
      ICohomo.idelesAtPlaces (K := K) (L := L) S = ⊤

/-- The finite set chosen in the source proof, including a prolongation of
each of its places.  The first three fields are exactly conditions (a), (b),
and (c). -/
structure AdmissiblePlacesData where
  S : Finset (NumberFieldPlace K)
  containsInfinite : ∀ v : InfinitePlace K,
    (Sum.inr v : NumberFieldPlace K) ∈ S
  containsRamified : ContainsRamifiedPlaces (K := K) (L := L) S
  containsClassGenerators :
    ContainsContractionsGenerators (K := K) (L := L) S
  w : ∀ v : S,
    CompletionPlacesAbove (L := L)
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))

/-- Arithmetic finiteness supplies a set satisfying the three conditions
listed in the proof of Theorem 4.3.  This bridge contains no cohomological or
Herbrand-quotient conclusion. -/
def AdmissiblePlacesBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    Nonempty (AdmissiblePlacesData (K := K) (L := L))

/-- Lemma 4.2 applied over `L`: condition (c), after passing to all places
above `S`, gives `I_L = Lˣ I_{L,T}`.  This bridge is purely an idèle/ideal
class comparison and contains no Herbrand-quotient assertion. -/
def GeneratorsIdelesBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NumberFieldPlace K)),
    ContainsContractionsGenerators (K := K) (L := L) S →
      GeneratesIdelesPrincipal (K := K) (L := L) S

/-- The quotient relation in the source proof.  The hypothesis is literally
`I_L = Lˣ I_{L,T}`, and the conclusion is the induced equivariant
identification `I_{L,T}/U(T) ≅ I_L/Lˣ`. -/
def RestrictedQuotientBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NumberFieldPlace K)),
    GeneratesIdelesPrincipal (K := K) (L := L) S →
      Nonempty
        (restrictedIdeleRepresentation (K := K) (L := L) S ≅
          classCokernelRepresentation (K := K) (L := L))

/-- The universe-polymorphic low-Tate form of multiplicativity for the exact
sequence

`0 → U(T) → I_{L,T} → C_L → 0`.

The representation isomorphism is an explicit argument, so this bridge says
only that Herbrand quotients are multiplicative in that exact sequence and
invariant under the displayed quotient identification. -/
def HerbrandExactBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    ∀ (S : Finset (NumberFieldPlace K))
      (_e : restrictedIdeleRepresentation (K := K) (L := L) S ≅
        classCokernelRepresentation (K := K) (L := L))
      (qU qI : ℚ),
      HerbrandQuotientValue
          (unitsPlacesRepresentation (K := K) (L := L) S) qU →
        HerbrandQuotientValue
          (idelesRepresentation (K := K) (L := L) S) qI →
        ∃ qC : ℚ,
          HerbrandQuotientValue
            (classCokernelRepresentation (K := K) (L := L)) qC ∧
          qI = qU * qC

/-- The source theorem follows from Propositions 2.7 and 3.1, the literal
choice of `S`, and the exact quotient relation above. -/
theorem statement_previous_results
    (h27 : LocalHerbrandFormula.{u})
    (h31 : PlacesHerbrandFormula.{u})
    (hplaces : AdmissiblePlacesBridge.{u})
    (hgenerates : GeneratorsIdelesBridge.{u})
    (hquotient : RestrictedQuotientBridge.{u})
    (hexact : HerbrandExactBridge.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
          letI : CommGroup Gal(L/K) := IsCyclic.commGroup
          HerbrandQuotientValue
            (classCokernelRepresentation (K := K) (L := L))
            (Module.finrank K L : ℚ)) := by
  intro K L _ _ _ _ _ _ _ _
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  obtain ⟨data⟩ := hplaces K L
  have hgeneration := hgenerates K L data.S data.containsClassGenerators
  obtain ⟨e⟩ := hquotient K L data.S hgeneration
  let P : ℚ := ∏ v : data.S, Nat.card
    (CompletionPlaceStabilizer
      (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (data.w v))
  have hI : HerbrandQuotientValue
      (idelesRepresentation (K := K) (L := L) data.S) P := by
    apply h27 K L data.S
    exact ⟨data.containsInfinite, data.containsRamified⟩
  obtain ⟨qU, hU, hdegree⟩ :=
    h31 K L data.S data.containsInfinite data.w
  obtain ⟨qC, hC, hmul⟩ :=
    hexact K L data.S e qU P hU hI
  have hqUpos : 0 < qU := by
    letI : Finite (tateZero
        (unitsPlacesRepresentation (K := K) (L := L) data.S)) := hU.1
    letI : Finite (tateNegOne
        (unitsPlacesRepresentation (K := K) (L := L) data.S)) := hU.2.1
    rw [← hU.2.2]
    exact div_pos
      (Nat.cast_pos.mpr Nat.card_pos)
      (Nat.cast_pos.mpr Nat.card_pos)
  have hqU : qU ≠ 0 := ne_of_gt hqUpos
  have hvalue : qC = (Module.finrank K L : ℚ) := by
    apply (mul_left_cancel₀ hqU)
    calc
      qU * qC = P := hmul.symm
      _ = (Module.finrank K L : ℚ) * qU := by
        dsimp only [P]
        rw [← Nat.cast_prod]
        exact hdegree.symm
      _ = qU * (Module.finrank K L : ℚ) := mul_comm _ _
  simpa only [hvalue] using hC

end

end Submission.CField.NIndex
