import Towers.ClassField.LocalClass.HerbrandQuotientsField
import Towers.ClassField.IdeleCohomology.CompletionInducedModule
import Towers.ClassField.IdeleCohomology.ConcreteIdeleAction

/-!
# Chapter VII, Section 2, Proposition 2.7

For a finite set `S` of places of `K`, this file models Milne's
`I_{L,T}` literally: its finite coordinate at `Q` must be a local unit when
the contracted prime of `Q` is not in `S`.  Infinite coordinates are always
unrestricted, just as in the restricted-product definition of the ideles.
-/

namespace Towers.CField.ICohomo

open IsDedekindDomain NumberField
open Representation
open scoped BigOperators
open Towers.NumberTheory.Milne
open Towers.CField.Shifting
open Towers.CField.LClass
open Towers.CField.Ideles

noncomputable section

universe u v

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The norm from coinvariants to invariants, repeated universe-polymorphically
because Mathlib's ordinary group-cohomology construction places the group and
coefficient ring in the same universe. -/
noncomputable def normCoinvariantsInvariants
    {k : Type v} {G : Type u} [CommRing k] [Group G] [Fintype G]
    (A : Rep k G) : A.ρ.Coinvariants →ₗ[k] A.ρ.invariants :=
  Coinvariants.lift A.ρ
    (A.ρ.norm.codRestrict A.ρ.invariants fun x => by
      rw [mem_invariants]
      exact fun g => A.ρ.self_norm_apply g x)
    fun g => LinearMap.ext fun x => Subtype.ext (A.ρ.norm_self_apply g x)

/-- Milne's `H_T^0(G,A)` in arbitrary universe. -/
abbrev tateZero {k : Type v} {G : Type u}
    [CommRing k] [Group G] [Fintype G] (A : Rep k G) :=
  A.ρ.invariants ⧸ LinearMap.range (normCoinvariantsInvariants A)

/-- Milne's `H_T^{-1}(G,A)` in arbitrary universe. -/
abbrev tateNegOne {k : Type v} {G : Type u}
    [CommRing k] [Group G] [Fintype G] (A : Rep k G) :=
  LinearMap.ker (normCoinvariantsInvariants A)

/-- Universe-polymorphic formulation that a representation has Herbrand
quotient `q`.  The older Chapter III wrapper is universe-zero because its
coefficient ring and group were originally placed in one universe; this
literal cardinal-ratio formulation applies to number fields in any universe. -/
def HerbrandQuotientValue {G : Type u} [CommGroup G] [Fintype G]
    (A : Rep ℤ G) (q : ℚ) : Prop :=
  Finite (tateZero A) ∧
    Finite (tateNegOne A) ∧
    (Nat.card (tateZero A) : ℚ) /
      Nat.card (tateNegOne A) = q

/-- The absolute value represented by a finite or infinite place. -/
def coinvariantsInvariantsAbsolute (v : NumberFieldPlace K) :
    AbsoluteValue K ℝ :=
  match v with
  | .inl v => (FinitePlace.mk v).val
  | .inr v => v.1

/-- Milne's subgroup `I_{L,T}` for the primes `T` of `L` above `S`.
Only the finite part occurs in the predicate, since all archimedean factors
of an idele are unrestricted. -/
def idelesAtPlaces (S : Finset (NumberFieldPlace K)) :
    Subgroup (IdeleGroup (RingOfIntegers L) L) where
  carrier := {x | ∀ Q : HeightOneSpectrum (RingOfIntegers L),
    (Sum.inl (Q.under (RingOfIntegers K)) : NumberFieldPlace K) ∉ S →
      x.2.1 Q ∈ IdeleUnitSubgroup (RingOfIntegers L) L Q}
  one_mem' := by
    intro Q _
    exact (IdeleUnitSubgroup (RingOfIntegers L) L Q).one_mem
  mul_mem' := by
    intro x y hx hy Q hQ
    exact (IdeleUnitSubgroup (RingOfIntegers L) L Q).mul_mem
      (hx Q hQ) (hy Q hQ)
  inv_mem' := by
    intro x hx Q hQ
    exact (IdeleUnitSubgroup (RingOfIntegers L) L Q).inv_mem
      (hx Q hQ)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Contracting a conjugate finite prime to the base field gives the same
prime. -/
theorem finite_prime_smul
    (sigma : Gal(L/K)) (Q : HeightOneSpectrum (RingOfIntegers L)) :
    letI := finitePrimeAction (K := K) (L := L)
    (sigma • Q).under (RingOfIntegers K) =
      Q.under (RingOfIntegers K) := by
  letI := finitePrimeAction (K := K) (L := L)
  apply HeightOneSpectrum.ext
  ext a
  change (RingOfIntegers.mapRingEquiv sigma.toRingEquiv).symm
      (algebraMap (RingOfIntegers K) (RingOfIntegers L) a) ∈ Q.asIdeal ↔
    algebraMap (RingOfIntegers K) (RingOfIntegers L) a ∈ Q.asIdeal
  have heq : (RingOfIntegers.mapRingEquiv sigma.toRingEquiv).symm
      (algebraMap (RingOfIntegers K) (RingOfIntegers L) a) =
      algebraMap (RingOfIntegers K) (RingOfIntegers L) a := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.mapRingEquiv_symm_apply]
    exact sigma.symm.commutes a
  rw [heq]

omit [FiniteDimensional K L] in
/-- `I_{L,T}` is stable under the concrete Galois action on ideles. -/
theorem ideles_smul
    (S : Finset (NumberFieldPlace K)) (sigma : Gal(L/K))
    (x : IdeleGroup (RingOfIntegers L) L) (hx : x ∈ idelesAtPlaces S) :
    letI := idelesGaloisAction (K := K) (L := L)
    sigma • x ∈ idelesAtPlaces S := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := L)
  letI := idelesGaloisAction (K := K) (L := L)
  intro Q hQ
  change (sigma • x.2).1 Q ∈
    IdeleUnitSubgroup (RingOfIntegers L) L Q
  rw [ideles_action_coordinate]
  apply transport_preserves_units
  apply hx
  intro hmem
  apply hQ
  simpa only [finite_prime_smul] using hmem

/-- The integral Galois representation on Milne's `I_{L,T}`. -/
@[implicit_reducible]
noncomputable def idelesDistribAction
    (S : Finset (NumberFieldPlace K)) :
    MulDistribMulAction Gal(L/K)
      (idelesAtPlaces (K := K) (L := L) S) := by
  letI := idelesGaloisAction (K := K) (L := L)
  exact
    { smul := fun sigma x =>
        ⟨sigma • (x : IdeleGroup (RingOfIntegers L) L),
          ideles_smul S sigma x x.2⟩
      one_smul := fun x => Subtype.ext
        (one_smul Gal(L/K) (x : IdeleGroup (RingOfIntegers L) L))
      mul_smul := fun sigma tau x =>
        Subtype.ext (mul_smul sigma tau
          (x : IdeleGroup (RingOfIntegers L) L))
      smul_one := fun sigma =>
        Subtype.ext (smul_one sigma :
          sigma • (1 : IdeleGroup (RingOfIntegers L) L) = 1)
      smul_mul := fun sigma x y =>
        Subtype.ext (smul_mul' sigma
          (x : IdeleGroup (RingOfIntegers L) L)
          (y : IdeleGroup (RingOfIntegers L) L)) }

/-- The representation whose Herbrand quotient occurs in Proposition 2.7. -/
noncomputable abbrev idelesRepresentation
    (S : Finset (NumberFieldPlace K)) : Rep ℤ Gal(L/K) :=
  let _ := idelesDistribAction (K := K) (L := L) S
  Rep.ofMulDistribMulAction Gal(L/K)
    (idelesAtPlaces (K := K) (L := L) S)

/-- The standing condition on `S` in the discussion preceding Proposition
VII.2.7: it contains every infinite place and every ramified finite place.
The finite condition is stated in the exact form consumed by the
finite-stage cohomology decomposition. -/
def AdmissiblePlaceSet
    (S : Finset (NumberFieldPlace K)) : Prop :=
  (∀ v : InfinitePlace K, (Sum.inr v : NumberFieldPlace K) ∈ S) ∧
    ∀ Q : HeightOneSpectrum (NumberField.RingOfIntegers L),
      Ideal.ramificationIdx
          (Q.under (NumberField.RingOfIntegers K)).asIdeal Q.asIdeal ≠ 1 →
        (Sum.inl (Q.under (NumberField.RingOfIntegers K)) :
          NumberFieldPlace K) ∈ S

/-- **Proposition VII.2.7 (source statement).**  A choice of one place of
`L` above each `v ∈ S` identifies `n_v` with the order of its decomposition
group.  The product is independent of these choices. -/
def LocalHerbrandFormula : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    ∀ (S : Finset (NumberFieldPlace K))
      (_hS : AdmissiblePlaceSet (K := K) (L := L) S)
      (w : ∀ v : S,
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))),
      HerbrandQuotientValue
        (idelesRepresentation (K := K) (L := L) S)
        (∏ v : S, Nat.card
          (CompletionPlaceStabilizer
            (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)))

/-- The local input to the proof: Proposition III.2.5, transported through
the canonical identification of a decomposition group with the Galois group
of the corresponding completion. -/
def LocalHerbrandBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    ∀ (v : NumberFieldPlace K)
      (w : CompletionPlacesAbove (L := L)
        (coinvariantsInvariantsAbsolute v)),
      letI : Fintype (CompletionPlaceStabilizer
        (coinvariantsInvariantsAbsolute v) w) := Fintype.ofFinite _
      HerbrandQuotientValue
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute v) w)
        (Nat.card (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute v) w))

/-- The remaining restricted-product assembly in Milne's proof.  It combines
Shapiro, multiplicativity of the Herbrand quotient, and the fact that the
product of the local-unit factors outside `S` has quotient one. -/
def HerbrandAssemblyBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
    letI : CommGroup Gal(L/K) := IsCyclic.commGroup
    ∀ (S : Finset (NumberFieldPlace K))
      (_hS : AdmissiblePlaceSet (K := K) (L := L) S)
      (w : ∀ v : S,
        CompletionPlacesAbove (L := L)
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K))),
      (∀ v : S,
        letI : Fintype (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)) :=
            Fintype.ofFinite _
        HerbrandQuotientValue
        (placeUnitsRepresentation
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v))
        (Nat.card (CompletionPlaceStabilizer
          (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)))) →
      HerbrandQuotientValue
        (idelesRepresentation (K := K) (L := L) S)
        (∏ v : S, Nat.card
          (CompletionPlaceStabilizer
            (coinvariantsInvariantsAbsolute (v : NumberFieldPlace K)) (w v)))

/-- Proposition 2.7 from its two precise inputs. -/
theorem coinvariants_invariants_assembly
    (hlocal : LocalHerbrandBridge.{u})
    (hassembly : HerbrandAssemblyBridge.{u}) :
    LocalHerbrandFormula.{u} := by
  intro K L _ _ _ _ _ _ _ _ S hS w
  apply hassembly K L S hS w
  intro v
  exact hlocal K L (v : NumberFieldPlace K) (w v)

end

end Towers.CField.ICohomo
