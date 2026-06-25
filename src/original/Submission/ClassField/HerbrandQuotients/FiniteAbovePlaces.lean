import Submission.ClassField.IdeleCohomology.NormInvariants
import Submission.ClassField.HerbrandQuotients.StableRepresentation
import Submission.ClassField.HerbrandQuotients.SUnits
import Submission.ClassField.Ideles.IdeleClassNorm

/-!
# Chapter VII, Section 3, Proposition 3.1

This file puts the actual `T`-unit group into the concrete Galois
representation constructed in Section 2.  The key stability argument is
local: completed Galois transport preserves the unit subgroup at every finite
place.
-/

namespace Submission.CField.HQuotie

open IsDedekindDomain NumberField Representation
open scoped BigOperators
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The finite primes of `L` lying over the finite members of `S`. -/
def primesAbovePlaces (S : Finset (NumberFieldPlace K)) :
    Set (FinitePrime L) :=
  {Q | (Sum.inl (Q.under (NumberField.RingOfIntegers K)) : NumberFieldPlace K) ∈ S}

/-- Milne's `U(T)` for the set of places above `S`.  Infinite places impose
no additional valuation condition, so only `primesAbovePlaces` enters
the `SUnits` definition. -/
abbrev unitsAtPlaces (S : Finset (NumberFieldPlace K)) :=
  SUnits L (primesAbovePlaces (K := K) (L := L) S)

/-- A global unit is a unit at `Q` exactly when its image in the completed
field belongs to the completed valuation-ring unit subgroup. -/
theorem place_embedding_subgroup
    (Q : FinitePrime L) (x : Lˣ) :
    Units.map (FinitePlace.embedding (K := L) Q) x ∈
        (Q.adicCompletionIntegers L).units ↔
      Q.valuation L x = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  change Valued.v (FinitePlace.embedding (K := L) Q (x : L)) = 1 ↔ _
  rw [FinitePlace.embedding_apply, Q.valuedAdicCompletion_eq_valuation']

omit [FiniteDimensional K L] [IsGalois K L] in
/-- A global element is a `T`-unit exactly when its principal idèle belongs
to `I_{L,T}`. -/
theorem principal_ideles_places
    (S : Finset (NumberFieldPlace K)) (x : Lˣ) :
    principalIdele (NumberField.RingOfIntegers L) L x ∈
        idelesAtPlaces (K := K) (L := L) S ↔
      x ∈ unitsAtPlaces (K := K) (L := L) S := by
  constructor
  · intro hx Q hQ
    have hxQ := hx Q hQ
    rw [principal_idele_finite] at hxQ
    exact (place_embedding_subgroup (L := L) Q x).1 hxQ
  · intro hx Q hQ
    rw [principal_idele_finite]
    exact (place_embedding_subgroup (L := L) Q x).2
      (hx Q hQ)

set_option maxHeartbeats 500000 in
-- Reuse the already constructed idèle action and its equivariant diagonal.
omit [FiniteDimensional K L] in
theorem units_places_smul
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K))
    (x : unitsAtPlaces (K := K) (L := L) S) :
    Units.map sigma.toRingEquiv.toRingHom.toMonoidHom (x : Lˣ) ∈
      unitsAtPlaces (K := K) (L := L) S := by
  let D := concreteActionData (K := K) (L := L)
  have hxIdele : principalIdele (NumberField.RingOfIntegers L) L (x : Lˣ) ∈
      idelesAtPlaces (K := K) (L := L) S :=
    (principal_ideles_places (K := K) (L := L) S x).2 x.property
  have hstable :
      (concreteActionData (K := K) (L := L)).action.smul sigma
          (principalIdele (NumberField.RingOfIntegers L) L (x : Lˣ)) ∈
        idelesAtPlaces (K := K) (L := L) S := by
    exact
      ((idelesDistribAction (K := K) (L := L) S).smul sigma
        ⟨principalIdele (NumberField.RingOfIntegers L) L (x : Lˣ), hxIdele⟩).property
  letI := idelesGaloisAction (K := K) (L := L)
  rw [show (concreteActionData (K := K) (L := L)).action.smul sigma
        (principalIdele (NumberField.RingOfIntegers L) L (x : Lˣ)) =
      principalIdele (NumberField.RingOfIntegers L) L
        (Units.map sigma.toRingEquiv.toRingHom.toMonoidHom (x : Lˣ)) by
      exact D.smul_principalIdele sigma (x : Lˣ)] at hstable
  exact (principal_ideles_places (K := K) (L := L) S _).1 hstable

set_option maxHeartbeats 500000 in
-- The action laws unfold the dependent stability proof above.
@[implicit_reducible]
noncomputable def placesDistribAction
    (S : Finset (NumberFieldPlace K)) :
    MulDistribMulAction Gal(L/K) (unitsAtPlaces (K := K) (L := L) S) where
  smul sigma x :=
    ⟨Units.map sigma.toRingEquiv.toRingHom.toMonoidHom (x : Lˣ),
      units_places_smul (K := K) (L := L) S sigma x⟩
  one_smul x := by
    apply Subtype.ext
    apply Units.ext
    rfl
  mul_smul sigma tau x := by
    apply Subtype.ext
    apply Units.ext
    rfl
  smul_one sigma := by
    apply Subtype.ext
    apply Units.ext
    exact congrArg Units.val
      (map_one (Units.map sigma.toRingEquiv.toRingHom.toMonoidHom))
  smul_mul sigma x y := by
    apply Subtype.ext
    apply Units.ext
    exact congrArg Units.val
      (map_mul (Units.map sigma.toRingEquiv.toRingHom.toMonoidHom)
        (x : Lˣ) (y : Lˣ))

/-- The representation on the actual `T`-unit group. -/
noncomputable abbrev unitsPlacesRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep ℤ Gal(L/K) :=
  let _ := placesDistribAction (K := K) (L := L) S
  Rep.ofMulDistribMulAction Gal(L/K) (unitsAtPlaces (K := K) (L := L) S)

/-- **Proposition VII.3.1 (source statement).**  The existential `q` records
both that the Herbrand quotient is defined and its value; the displayed
identity is exactly `n * h(U(T)) = ∏_{v∈S} n_v`. -/
def PlacesHerbrandFormula : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    ∀ (S : Finset (NumberFieldPlace K))
      (_hSinf : ∀ v : InfinitePlace K,
        (Sum.inr v : NumberFieldPlace K) ∈ S)
      (w : ∀ v : S,
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))),
      ∃ q : ℚ,
        HerbrandQuotientValue
          (unitsPlacesRepresentation (K := K) (L := L) S) q ∧
        (Module.finrank K L : ℚ) * q =
          ∏ v : S, Nat.card
            (CompletionPlaceStabilizer
              (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))

/-- A representation cannot have two different Herbrand-quotient values. -/
theorem herbrand_value_unique
    {G : Type u} [CommGroup G] [Fintype G]
    {A : Rep ℤ G} {q r : ℚ}
    (hq : HerbrandQuotientValue A q)
    (hr : HerbrandQuotientValue A r) : q = r :=
  hq.2.2.symm.trans hr.2.2

/-- The remaining arithmetic construction in Milne's proof of Proposition
3.1.  It asks for the two actual kinds of lattices used there:

* `N`, the permutation lattice on the places above `S`, whose quotient is
  the product of the decomposition-group orders;
* `M = log(U(T)) + ℤ e`, whose quotient is `[L:K]` times that of `U(T)`.

The common ambient real representation and the full-lattice hypotheses are
kept explicit, so Lemma 3.5—not this bridge—supplies equality of their
Herbrand quotients. -/
def ArithmeticLatticesBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    ∀ (S : Finset (NumberFieldPlace K))
      (_hSinf : ∀ v : InfinitePlace K,
        (Sum.inr v : NumberFieldPlace K) ∈ S)
      (w : ∀ v : S,
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))),
      ∃ (V : ModuleCat.{u} ℝ)
        (rho : Representation ℝ Gal(L/K) V)
        (M N : Submodule ℤ V)
        (hMstable : ∀ g x, x ∈ M → rho g x ∈ M)
        (hNstable : ∀ g x, x ∈ N → rho g x ∈ N),
        FullRealLattice M ∧
          FullRealLattice N ∧
          HerbrandQuotientValue
            (stableLatticeRepresentation rho N hNstable)
            (∏ v : S, Nat.card
              (CompletionPlaceStabilizer
                (coinvariantsInvariantsAbsolute
                  (v : NumberFieldPlace K)) (w v))) ∧
          ∀ q : ℚ,
            HerbrandQuotientValue
                (stableLatticeRepresentation rho M hMstable) q ↔
              ∃ qU : ℚ,
                HerbrandQuotientValue
                  (unitsPlacesRepresentation (K := K) (L := L) S) qU ∧
                q = (Module.finrank K L : ℚ) * qU

-- Elaborating the two dependent stable-lattice representations is expensive.
set_option maxHeartbeats 5000000 in
-- Elaborating the two dependent stable-lattice representations is expensive.
theorem above_places_lattices
    (hlattices : ArithmeticLatticesBridge.{u}) :
    PlacesHerbrandFormula.{u} := by
  intro K L _ _ _ _ _ _ _ _ S hSinf w
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  obtain ⟨V, rho, M, N, hMstable, hNstable,
      hMfull, hNfull, hN, hM_units⟩ :=
    hlattices K L S hSinf w
  have hcompare :=
    stable_representation_isogenies
      Gal(L/K) V rho M N hMstable hNstable hMfull hNfull
  obtain ⟨qM, hM, hNqM⟩ := hcompare.2 (by
    refine ⟨∏ v : S, (Nat.card
      (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))
        (w v)) : ℚ), ?_⟩
    exact hN)
  obtain ⟨qU, hU, hqM⟩ := (hM_units qM).mp hM
  refine ⟨qU, hU, ?_⟩
  calc
    (Module.finrank K L : ℚ) * qU = qM := hqM.symm
    _ = ∏ v : S, Nat.card
          (CompletionPlaceStabilizer
            (coinvariantsInvariantsAbsolute
              (v : NumberFieldPlace K)) (w v)) :=
      by
        simpa using herbrand_value_unique hNqM hN

end

end Submission.CField.HQuotie
