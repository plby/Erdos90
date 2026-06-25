import Submission.ClassField.KummerTheory.KummerOrderCorrespondence
import Submission.ClassField.KummerNormIndex.SUnitUnramified
import Submission.ClassField.KummerNormIndex.SecondInequalityAssembly
import Submission.ClassField.KummerNormIndex.CyclotomicBaseChange

open scoped IsMulCommutative

/-!
# The Kummer tower used in the second inequality

Starting from a finite abelian exponent-`p` subextension, this file embeds
its radical power classes into the S-unit power classes selected before
Lemma VII.6.2.  It also records the two degree-as-a-power-of-`p`
calculations which give `r + t = |S|`.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.KTheory
open Submission.CField.NIndex
open Submission.CField.HNorm

noncomputable section

universe u

/-- Condition (d) in Milne's choice of `S` puts every radical class for
`L` in the subgroup of S-unit power classes. -/
theorem radical_s_class
    (p : ℕ) (hp : p.Prime)
    (K Omega : Type u) [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega] [IsAlgClosure K Omega]
    (hroots : (primitiveRoots p K).Nonempty)
    (L : AESubext K Omega p)
    (D : SecondInequalityData p K
      (radicalSubgroup p hp.pos hroots L)) :
    (radicalSubgroup p hp.pos hroots L).carrier ≤
      (sUnitSubgroup K p hp hroots D.S
        D.containsInfinite).carrier := by
  intro b hb
  change b ∈ sUnitCarrier K p D.S
  let bL : (radicalSubgroup p hp.pos hroots L).carrier := ⟨b, hb⟩
  let a : ArithmeticSUnits K (finitePrimePart K D.S) :=
    ⟨powerClassRepresentative K p b,
      D.representativesSUnits bL⟩
  refine ⟨a, ?_⟩
  exact power_class_representative K p b

/-- Hence the original exponent-`p` extension is contained in
`M = K[U(S)^(1/p)]`. -/
theorem subextension_s_kummer
    (p : ℕ) (hp : p.Prime)
    (K Omega : Type u) [Field K] [NumberField K]
    [Field Omega] [Algebra K Omega] [IsAlgClosure K Omega]
    (hroots : (primitiveRoots p K).Nonempty)
    (L : AESubext K Omega p)
    (D : SecondInequalityData p K
      (radicalSubgroup p hp.pos hroots L)) :
    L.carrier ≤ sKummerField K Omega p hp hroots D.S
      D.containsInfinite := by
  rw [← kummer_radical_subgroup
    (K := K) (Omega := Omega) p hp.pos hroots L]
  exact kummerField_mono hp.pos
    (radical_s_class
      p hp K Omega hroots L D)

/-- A finite Galois extension whose abelian Galois group is killed by the
prime `p` has degree `p` to the dimension of that Galois group over
`ZMod p`. -/
theorem finrank_pow_galois
    (p : ℕ) (hp : p.Prime)
    (K E : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (hexponent : ∀ sigma : Gal(E/K), sigma ^ p = 1) :
    letI : CommGroup Gal(E/K) := inferInstance
    letI : Module (ZMod p) (Additive Gal(E/K)) :=
      exponentPModule p hexponent
    Module.finrank K E =
      p ^ Module.finrank (ZMod p) (Additive Gal(E/K)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup Gal(E/K) := inferInstance
  letI : Module (ZMod p) (Additive Gal(E/K)) :=
    exponentPModule p hexponent
  rw [← IsGalois.card_aut_eq_finrank K E]
  calc
    Nat.card Gal(E/K) = Nat.card (Additive Gal(E/K)) := rfl
    _ = Nat.card (ZMod p) ^
        Module.finrank (ZMod p) (Additive Gal(E/K)) :=
      Module.natCard_eq_pow_finrank
    _ = p ^ Module.finrank (ZMod p) (Additive Gal(E/K)) := by
      rw [Nat.card_zmod]

/-- The set of primes exposed by Lemma VII.6.2 has cardinality equal to
the `ZMod p`-dimension of `Gal(M/L)`, because its Frobenius elements are a
basis indexed bijectively by that set. -/
theorem frobenius_basis_finrank
    (p : ℕ) (hp : p.Prime) (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois L M] [IsAbelianGalois K M]
    (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K))
    (hT : FrobeniusBasis
      (K := K) (L := L) (M := M) p hexponent S T) :
    letI : IsMulCommutative Gal(M/L) :=
      gal_ml_commutative (K := K) (L := L) (M := M)
    letI : CommGroup Gal(M/L) := inferInstance
    letI : Module (ZMod p) (Additive Gal(M/L)) :=
      exponentPModule p (gal_ml_pow
        (K := K) (L := L) (M := M) p hexponent)
    T.card = Module.finrank (ZMod p) (Additive Gal(M/L)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsMulCommutative Gal(M/L) :=
    gal_ml_commutative (K := K) (L := L) (M := M)
  letI : CommGroup Gal(M/L) := inferInstance
  letI : Module (ZMod p) (Additive Gal(M/L)) :=
    exponentPModule p (gal_ml_pow
      (K := K) (L := L) (M := M) p hexponent)
  rcases hT with ⟨i, fi, indexPrime, _w, b, hindex, _⟩
  letI : Fintype i := fi
  let eIndex : i ≃ T := Equiv.ofBijective indexPrime hindex
  calc
    T.card = Fintype.card T := by simp
    _ = Fintype.card i := (Fintype.card_congr eIndex).symm
    _ = Module.finrank (ZMod p) (Additive Gal(M/L)) :=
      (Module.finrank_eq_card_basis b).symm

set_option maxHeartbeats 3000000 in
-- The dependent Frobenius-basis witness and completed norm factors elaborate together.
/-- The primes selected by Lemma VII.6.2 are locally trivial in `L / K`.

Each basis vector is nonzero, hence its `M / L` Frobenius is nontrivial.
The inertia-degree argument in `splits_completely_ne`
then shows that its contracted base prime splits completely in `L`.  A
single completed factor therefore supplies a norm preimage of every local
unit. -/
theorem selected_locally_trivial
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsAbelianGalois K L] [IsGalois L M] [IsAbelianGalois K M]
    (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K))
    (hunramified : ∀ Q : FinitePrime M,
      (Sum.inl (Q.under (NumberField.RingOfIntegers K)) :
        NumberFieldPlace K) ∉ S →
        Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal)
    (T : Finset (FinitePrime K))
    (hT : FrobeniusBasis
      (K := K) (L := L) (M := M) p hexponent S T) :
    SelectedLocallyTrivial K L T := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsMulCommutative Gal(M/L) :=
    gal_ml_commutative (K := K) (L := L) (M := M)
  letI : CommGroup Gal(M/L) := inferInstance
  letI : Module (ZMod p) (Additive Gal(M/L)) :=
    exponentPModule p (gal_ml_pow
      (K := K) (L := L) (M := M) p hexponent)
  rcases hT with
    ⟨i, fi, indexPrime, w, b, hindex, hDisjoint, hunder,
      hbasis, _hcompat⟩
  letI : Fintype i := fi
  intro P hPT x
  let PT : T := ⟨P, hPT⟩
  obtain ⟨j, hj⟩ := hindex.2 PT
  have hjP : (indexPrime j : FinitePrime K) = P :=
    congrArg Subtype.val hj
  have hwP : (w j).under (NumberField.RingOfIntegers K) = P :=
    (hunder j).trans hjP
  have hQnotS :
      (Sum.inl ((w j).under (NumberField.RingOfIntegers K)) :
        NumberFieldPlace K) ∉ S := by
    simpa only [hwP] using hDisjoint P hPT
  have hFrobNe : numberFrobeniusElement (K := L) (w j) ≠ 1 := by
    intro hFrob
    have hbzero : b j = 0 := by
      rw [hbasis j, hFrob]
      rfl
    exact b.ne_zero j hbzero
  have hsplitQ : SplitsCompletelyAt K L
      ((w j).under (NumberField.RingOfIntegers K)) :=
    splits_completely_ne p hp K L M
      hexponent S hunramified (w j) hQnotS hFrobNe
  have hsplit : SplitsCompletelyAt K L P := by
    simpa only [hwP] using hsplitQ
  let Q := chosenPrimeFactor (K := K) (L := L) P
  have hsurjective :=
    surjective_splits_completely P Q hsplit
  obtain ⟨y, hy⟩ := hsurjective x
  exact lift_completion_range
    (K := K) (L := L) P Q x ⟨y, hy⟩

section SetupConstruction

variable (K Omega : Type u) [Field K] [NumberField K]
  [Field Omega] [Algebra K Omega] [IsAlgClosure K Omega]

/-- A finite Kummer subfield of an algebraic closure is a number field. -/
@[implicit_reducible]
noncomputable def kummerFieldNumber
    (p : ℕ) (hp : p.Prime) (B : PCSubgro K p) :
    NumberField (kummerField K Omega p hp.pos B) := by
  letI : FiniteDimensional K (kummerField K Omega p hp.pos B) :=
    dimensional_kummer_field K Omega p hp.pos B
  exact NumberField.of_module_finite K (kummerField K Omega p hp.pos B)

/-- The finite Kummer field attached to a subgroup of power classes is an
abelian Galois extension when the base contains the `p`th roots of unity. -/
@[implicit_reducible]
noncomputable def kummerAbelianGalois
    (p : ℕ) (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (B : PCSubgro K p) :
    IsAbelianGalois K (kummerField K Omega p hp.pos B) := by
  let zeta : K := hroots.choose
  have hzeta : IsPrimitiveRoot zeta p :=
    (mem_primitiveRoots hp.pos).mp hroots.choose_spec
  letI : FiniteDimensional K (kummerField K Omega p hp.pos B) :=
    dimensional_kummer_field K Omega p hp.pos B
  letI : IsGalois K (kummerField K Omega p hp.pos B) :=
    kummer_galois K Omega p hp.pos hzeta B
  letI : IsMulCommutative Gal(kummerField K Omega p hp.pos B/K) :=
    ⟨⟨fun sigma tau ↦ kummer_galois_commute
      K Omega p hp.pos hzeta B sigma tau⟩⟩
  exact
    { toIsGalois := inferInstance
      toIsMulCommutative := inferInstance }

set_option maxHeartbeats 3000000 in
-- The resulting structure carries both Kummer fields and three compatible
-- field-extension instance chains.
/-- The complete auxiliary Kummer setup preceding Lemma VII.6.2, for a
literal finite subgroup `B ≤ Kˣ/Kˣᵖ`.  No part of the setup is assumed:
`S`, `M`, the inclusion, the ramification assertions, and `r+t=|S|` are
all constructed from `B`. -/
noncomputable def secondInequalitySetup
    (p : ℕ) (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (B : PCSubgro K p)
    (D : SecondInequalityData p K B) :
    let L := kummerField K Omega p hp.pos B
    letI : FiniteDimensional K L :=
      dimensional_kummer_field K Omega p hp.pos B
    letI : NumberField L := kummerFieldNumber K Omega p hp B
    letI : IsAbelianGalois K L :=
      kummerAbelianGalois K Omega p hp hroots B
    SISetup p K L := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let L := kummerField K Omega p hp.pos B
  letI : FiniteDimensional K L :=
    dimensional_kummer_field K Omega p hp.pos B
  letI : NumberField L := kummerFieldNumber K Omega p hp B
  letI : IsAbelianGalois K L :=
    kummerAbelianGalois K Omega p hp hroots B
  let C := sUnitSubgroup K p hp hroots D.S D.containsInfinite
  let M := sKummerField K Omega p hp hroots D.S D.containsInfinite
  have hBC : B.carrier ≤ C.carrier := by
    intro b hb
    change b ∈ sUnitCarrier K p D.S
    let bB : B.carrier := ⟨b, hb⟩
    let a : ArithmeticSUnits K (finitePrimePart K D.S) :=
      ⟨powerClassRepresentative K p b,
        D.representativesSUnits bB⟩
    exact ⟨a, power_class_representative K p b⟩
  have hLM : L ≤ M := by
    exact kummerField_mono hp.pos hBC
  letI : FiniteDimensional K M :=
    sKummerDimensional K Omega p hp hroots D.S
      D.containsInfinite
  letI : NumberField M :=
    sKummerNumber K Omega p hp hroots D.S
      D.containsInfinite
  letI : IsAbelianGalois K M :=
    sAbelianGalois K Omega p hp hroots D.S
      D.containsInfinite
  letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  letI : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : FiniteDimensional L M := FiniteDimensional.right K L M
  letI : Module.Free L M := Module.Free.of_divisionRing L M
  letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have exponentL : ∀ sigma : Gal(L/K), sigma ^ p = 1 := by
    let zeta : K := hroots.choose
    have hzeta : IsPrimitiveRoot zeta p :=
      (mem_primitiveRoots hp.pos).mp hroots.choose_spec
    exact kummer_field_galois K Omega p hp.pos hzeta B
  have exponentM : ∀ sigma : Gal(M/K), sigma ^ p = 1 :=
    s_kummer_galois
      K Omega p hp hroots D.S D.containsInfinite
  letI : CommGroup Gal(L/K) := inferInstance
  letI : Module (ZMod p) (Additive Gal(L/K)) :=
    exponentPModule p exponentL
  letI : IsMulCommutative Gal(M/L) :=
    gal_ml_commutative (K := K) (L := L) (M := M)
  letI : CommGroup Gal(M/L) := inferInstance
  letI : Module (ZMod p) (Additive Gal(M/L)) :=
    exponentPModule p (gal_ml_pow
      (K := K) (L := L) (M := M) p exponentM)
  let r := Module.finrank (ZMod p) (Additive Gal(L/K))
  let t := Module.finrank (ZMod p) (Additive Gal(M/L))
  have degreeKL : Module.finrank K L = p ^ r := by
    exact finrank_pow_galois p hp K L exponentL
  have degreeLM : Module.finrank L M = p ^ t := by
    exact finrank_pow_galois p hp L M
      (gal_ml_pow (K := K) (L := L) (M := M) p exponentM)
  have degreeKM : Module.finrank K M = p ^ D.S.card := by
    exact finrank_s_kummer K Omega p hp hroots D.S
      D.containsInfinite
  have cardS : D.S.card = r + t := by
    apply Nat.pow_right_injective hp.two_le
    calc
      p ^ D.S.card = Module.finrank K M := degreeKM.symm
      _ = Module.finrank K L * Module.finrank L M :=
        (Module.finrank_mul_finrank K L M).symm
      _ = p ^ r * p ^ t := by rw [degreeKL, degreeLM]
      _ = p ^ (r + t) := (pow_add p r t).symm
  have unramifiedM : ∀ Q : FinitePrime M,
      (Sum.inl (Q.under (NumberField.RingOfIntegers K)) :
        NumberFieldPlace K) ∉ D.S →
        Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal :=
    s_kummer_outside K Omega p hp hroots D.S
      D.containsInfinite D.containsDivisors
  have unramifiedL : ∀ Q : FinitePrime L,
      (Sum.inl (Q.under (NumberField.RingOfIntegers K)) :
        NumberFieldPlace K) ∉ D.S →
        Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal :=
    outside_representatives_s
      K Omega p hp hroots B D.S D.containsDivisors
        D.representativesSUnits
  refine
    { M := M
      fieldM := inferInstance
      numberFieldM := inferInstance
      algebraLM := inferInstance
      algebraKM := inferInstance
      scalarTower := inferInstance
      finiteDimensionalLM := inferInstance
      isGaloisLM := inferInstance
      abelianGaloisKM := inferInstance
      S := D.S
      r := r
      t := t
      degreeKL := degreeKL
      cardS := cardS
      containsInfinite := D.containsInfinite
      containsDivisors := D.containsDivisors
      containsClassGenerators := D.containsClassGenerators
      exponentL := exponentL
      exponentM := exponentM
      unramifiedMOutside := unramifiedM
      unramifiedLOutside := unramifiedL
      containsSRoots :=
        contains_pth_roots
          K Omega p hp hroots D.S D.containsInfinite
      generatedSRoots :=
        generated_pth_roots
          K Omega p hp hroots D.S D.containsInfinite
      frobeniusBasisCard := by
        intro T hT
        exact frobenius_basis_finrank
          p hp K L M exponentM D.S T hT
      selectedPlacesLocally := by
        intro T hT
        exact selected_locally_trivial
          p hp K L M exponentM D.S unramifiedM T hT }

end SetupConstruction

set_option synthInstance.maxHeartbeats 1000000 in
-- The algebraic-closure image, Kummer field, and transported tower overlap heavily.
set_option maxHeartbeats 6000000 in
/-- Milne's auxiliary Kummer tower exists for every abelian extension of
prime degree once the base contains the `p`th roots of unity.  The original
field is embedded into an algebraic closure, Kummer correspondence places
its image in `K[U(S)^(1/p)]`, and that inclusion is transported back to a
literal `K → L → M` tower. -/
theorem second_inequality_setup
    (p : ℕ) (hp : p.Prime)
    (K L : Type u)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    (hroots : (primitiveRoots p K).Nonempty)
    (hdegree : Module.finrank K L = p) :
    Nonempty (SISetup p K L) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let Omega := AlgebraicClosure L
  letI : Algebra K Omega := inferInstance
  letI : IsAlgClosure K Omega := inferInstance
  let i : L →ₐ[K] Omega := IsScalarTower.toAlgHom K L Omega
  let E0 : IntermediateField K Omega := i.fieldRange
  let e : L ≃ₐ[K] E0 := AlgEquiv.ofInjectiveField i
  letI : FiniteDimensional K E0 :=
    FiniteDimensional.of_surjective
      e.toLinearEquiv.toLinearMap e.surjective
  letI : IsGalois K E0 := IsGalois.of_algEquiv e
  let eAut : Gal(L/K) ≃* Gal(E0/K) := e.autCongr
  letI : IsMulCommutative Gal(E0/K) :=
    ⟨⟨fun sigma tau ↦ by
      apply eAut.symm.injective
      simpa only [map_mul] using
        mul_comm (eAut.symm sigma) (eAut.symm tau)⟩⟩
  have exponentL : ∀ sigma : Gal(L/K), sigma ^ p = 1 := by
    intro sigma
    rw [← hdegree, ← IsGalois.card_aut_eq_finrank K L]
    exact pow_card_eq_one'
  have exponentE : ∀ sigma : Gal(E0/K), sigma ^ p = 1 := by
    intro sigma
    apply eAut.symm.injective
    simpa only [map_pow, map_one] using exponentL (eAut.symm sigma)
  let E : AESubext K Omega p :=
    { carrier := E0
      exponent_dvd := exponentE }
  let B : PCSubgro K p :=
    radicalSubgroup p hp.pos hroots E
  let D : SecondInequalityData p K B :=
    Classical.choice (second_inequality_places p hp K B)
  let M := sKummerField K Omega p hp hroots D.S D.containsInfinite
  letI : FiniteDimensional K M :=
    sKummerDimensional
      K Omega p hp hroots D.S D.containsInfinite
  letI : NumberField M :=
    sKummerNumber
      K Omega p hp hroots D.S D.containsInfinite
  letI : IsAbelianGalois K M :=
    sAbelianGalois
      K Omega p hp hroots D.S D.containsInfinite
  have hEM : E.carrier ≤ M :=
    subextension_s_kummer p hp K Omega hroots E D
  let jL : L →ₐ[K] M :=
    (IntermediateField.inclusion hEM).comp e.toAlgHom
  letI : Algebra L M := jL.toRingHom.toAlgebra
  letI : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change (algebraMap K M) x = jL (algebraMap K L x)
      exact (jL.commutes x).symm
  letI : FiniteDimensional L M := FiniteDimensional.right K L M
  letI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  have degreeM : Module.finrank K M = p ^ D.S.card :=
    finrank_s_kummer
      K Omega p hp hroots D.S D.containsInfinite
  have exponentM : ∀ sigma : Gal(M/K), sigma ^ p = 1 :=
    s_kummer_galois
      K Omega p hp hroots D.S D.containsInfinite
  have unramifiedM : ∀ Q : FinitePrime M,
      (Sum.inl (Q.under (NumberField.RingOfIntegers K)) :
        NumberFieldPlace K) ∉ D.S →
        Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal :=
    s_kummer_outside
      K Omega p hp hroots D.S D.containsInfinite D.containsDivisors
  have unramifiedL : ∀ Q : FinitePrime L,
      (Sum.inl (Q.under (NumberField.RingOfIntegers K)) :
        NumberFieldPlace K) ∉ D.S →
        Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal := by
    intro Q hQ
    let qM := chosenPrimeFactor (K := L) (L := M) Q
    let R : FinitePrime M := upperPrime (K := L) (L := M) Q qM
    have hRunderL : R.under (NumberField.RingOfIntegers L) = Q :=
      upperPrime_under (K := L) (L := M) Q qM
    have hRunderK : R.under (NumberField.RingOfIntegers K) =
        Q.under (NumberField.RingOfIntegers K) := by
      apply HeightOneSpectrum.ext
      calc
        R.asIdeal.under (NumberField.RingOfIntegers K) =
            (R.asIdeal.under (NumberField.RingOfIntegers L)).under
              (NumberField.RingOfIntegers K) :=
          (Ideal.under_under R.asIdeal).symm
        _ = Q.asIdeal.under (NumberField.RingOfIntegers K) := by
          have hIdeal :
              R.asIdeal.under (NumberField.RingOfIntegers L) = Q.asIdeal :=
            congrArg HeightOneSpectrum.asIdeal hRunderL
          exact congrArg
            (fun I : Ideal (NumberField.RingOfIntegers L) ↦
              I.under (NumberField.RingOfIntegers K)) hIdeal
    letI : Algebra.IsUnramifiedAt
        (NumberField.RingOfIntegers K) R.asIdeal :=
      unramifiedM R (by simpa only [hRunderK] using hQ)
    letI : R.asIdeal.LiesOver Q.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal hRunderL).symm⟩
    exact Algebra.IsUnramifiedAt.of_liesOver
      (NumberField.RingOfIntegers K) Q.asIdeal R.asIdeal
  have cardS : D.S.card = 1 + (D.S.card - 1) := by
    let v : InfinitePlace K :=
      Classical.choice (inferInstance : Nonempty (InfinitePlace K))
    have hv : (Sum.inr v : NumberFieldPlace K) ∈ D.S :=
      D.containsInfinite v
    have hpositive : 0 < D.S.card := Finset.card_pos.mpr ⟨_, hv⟩
    omega
  have frobeniusCard : ∀ T : Finset (FinitePrime K),
      FrobeniusBasis
        (K := K) (L := L) (M := M) p exponentM D.S T →
        T.card = D.S.card - 1 := by
    intro T hT
    have hLMdegree : Module.finrank L M = p ^ T.card := by
      rw [← IsGalois.card_aut_eq_finrank L M]
      exact galois_card_eq p K L M exponentM D.S T hT
    have hpow : p ^ D.S.card = p ^ (T.card + 1) := by
      calc
        p ^ D.S.card = Module.finrank K M := degreeM.symm
        _ = Module.finrank K L * Module.finrank L M :=
          (Module.finrank_mul_finrank K L M).symm
        _ = p * p ^ T.card := by rw [hdegree, hLMdegree]
        _ = p ^ (T.card + 1) := by simp [pow_succ, mul_comm]
    have hcards : D.S.card = T.card + 1 :=
      Nat.pow_right_injective hp.two_le hpow
    omega
  exact ⟨
    { M := M
      fieldM := inferInstance
      numberFieldM := inferInstance
      algebraLM := inferInstance
      algebraKM := inferInstance
      scalarTower := inferInstance
      finiteDimensionalLM := inferInstance
      isGaloisLM := inferInstance
      abelianGaloisKM := inferInstance
      S := D.S
      r := 1
      t := D.S.card - 1
      degreeKL := by simpa using hdegree
      cardS := cardS
      containsInfinite := D.containsInfinite
      containsDivisors := D.containsDivisors
      containsClassGenerators := D.containsClassGenerators
      exponentL := exponentL
      exponentM := exponentM
      unramifiedMOutside := unramifiedM
      unramifiedLOutside := unramifiedL
      containsSRoots :=
        contains_pth_roots
          K Omega p hp hroots D.S D.containsInfinite
      generatedSRoots :=
        generated_pth_roots
          K Omega p hp hroots D.S D.containsInfinite
      frobeniusBasisCard := frobeniusCard
      selectedPlacesLocally := by
        intro T hT
        exact selected_locally_trivial
          p hp K L M exponentM D.S unramifiedM T hT }⟩

/-- The algebraic argument of §VII.6 proves the second inequality for a
prime-degree cyclic extension whose base already contains the relevant
roots of unity. -/
theorem inequality_primitive_roots
    (p : ℕ) (hp : p.Prime)
    (K L : Type u)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    (hroots : (primitiveRoots p K).Nonempty)
    (hdegree : Module.finrank K L = p) :
    SecondInequalityAt K L := by
  letI : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  obtain ⟨D⟩ := second_inequality_setup
    p hp K L hroots hdegree
  exact D.secondInequality hp hroots

/-- The unconditional prime-degree cyclic second inequality.  Lemma
VII.6.1 removes the primitive-root hypothesis from the Kummer proof. -/
theorem second_inequality_cyclic
    (p : ℕ) (hp : p.Prime)
    (K L : Type u)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    (hdegree : Module.finrank K L = p) :
    SecondInequalityAt K L := by
  exact cyclotomicChangeStatement p hp
    (fun K L _ _ _ _ _ _ _ _ hroots hdegree ↦
      inequality_primitive_roots
        p hp K L hroots hdegree)
    K L hdegree

end

end Submission.CField.KNIndex
