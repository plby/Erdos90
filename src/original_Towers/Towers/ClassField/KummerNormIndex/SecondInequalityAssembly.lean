import Towers.ClassField.NormIndex.IndexComparison
import Towers.ClassField.KummerNormIndex.IdeleClassQuotient
import Towers.ClassField.KummerNormIndex.CompletionRestriction
import Towers.ClassField.KummerNormIndex.LocalNormBridges
import Towers.ClassField.KummerNormIndex.LocalPowerIndex
import Towers.ClassField.KummerNormIndex.IntersectionPower
import Towers.ClassField.KummerNormIndex.KummerPairing
import Towers.ClassField.BrauerLocalization.IdeleIdealSupport

/-!
# Completion of the algebraic second-inequality argument

This file assembles the subgroup-index calculation following Lemma VII.6.4.
The first theorem identifies the intersection factor in Lemma VII.6.5 with
the literal `S ∪ T`-unit quotient computed in Lemma VII.6.7.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HQuotie
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (OK K) K

private theorem finite_prime_self
    (K : Type u) [Field K] [NumberField K] (P : FinitePrime K) :
    P.under (OK K) = P := by
  apply HeightOneSpectrum.ext
  ext x
  simp [Ideal.under_def]

/-- The `Kˣ`-intersection factor in Lemma VII.6.5 is exactly the index of
the subgroup called `Kˣ ∩ E` inside the `S ∪ T`-unit group in Lemma
VII.6.7. -/
theorem principal_intersection_rel
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K)) :
    ((ideleSubgroup K p S T) ⊓
        principalIdeles (OK K) K).relIndex
      ((idelesAtPlaces (K := K) (L := K)
          (combinedPlaces K S T)) ⊓
        principalIdeles (OK K) K) =
      (principalIntersection K p S T).index := by
  classical
  let E := ideleSubgroup K p S T
  let I := idelesAtPlaces (K := K) (L := K)
    (combinedPlaces K S T)
  let C := principalIdeles (OK K) K
  let U := sUnits K S T
  let f : U →* IK K := principalIdeleHom K S T
  have hf : Function.Injective f :=
    (principalIdele_injective (OK K) K).comp
      (Set.unit (finitePrimePart K
        (combinedPlaces K S T)) K).subtype_injective
  have hEI : E ≤ I := by
    intro x hx P hP
    change (Sum.inl (P.under (OK K)) : NumberFieldPlace K) ∉
      combinedPlaces K S T at hP
    rw [finite_prime_self K P] at hP
    have hPS : (Sum.inl P : NumberFieldPlace K) ∉ S := by
      intro h
      exact hP (Finset.mem_union_left _ h)
    have hPT : P ∉ T := by
      intro h
      exact hP (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨P, h, rfl⟩))
    exact hx.2.2 P hPS hPT
  have htop : (⊤ : Subgroup U).map f = I ⊓ C := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      constructor
      · apply (principal_ideles_places
          (K := K) (L := K) (combinedPlaces K S T) (y : Kˣ)).2
        simp [U, sUnits, finitePrimePart]
      · exact ⟨(y : Kˣ), rfl⟩
    · rintro ⟨hxI, ⟨y, rfl⟩⟩
      have hyUnits : y ∈ unitsAtPlaces (K := K) (L := K)
          (combinedPlaces K S T) :=
        (principal_ideles_places
          (K := K) (L := K) (combinedPlaces K S T) y).1 hxI
      let z : U := ⟨y, by
        simpa [U, sUnits, finitePrimePart,
          primesAbovePlaces, finite_prime_self] using
          hyUnits⟩
      exact ⟨z, trivial, rfl⟩
  have hintersection :
      (principalIntersection K p S T).map f = E ⊓ C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, ⟨(y : Kˣ), rfl⟩⟩
    · rintro ⟨hxE, ⟨y, rfl⟩⟩
      have hyI : principalIdele (OK K) K y ∈ I := hEI hxE
      have hyUnits : y ∈ unitsAtPlaces (K := K) (L := K)
          (combinedPlaces K S T) :=
        (principal_ideles_places
          (K := K) (L := K) (combinedPlaces K S T) y).1 hyI
      let z : U := ⟨y, by
        simpa [U, sUnits, finitePrimePart,
          primesAbovePlaces, finite_prime_self] using
          hyUnits⟩
      refine ⟨z, ?_, rfl⟩
      exact hxE
  rw [← hintersection, ← htop,
    Subgroup.relIndex_map_map_of_injective _ _ hf,
    Subgroup.relIndex_top_right]

/-- The auxiliary data introduced immediately before Lemma VII.6.2.

This is Milne's choice of `S`, the Kummer extension
`M = K[U(S)^(1/p)]`, and the numerical relation
`r + t = |S|`.  The final two fields record the two consequences stated
after Lemma VII.6.2: `|T| = t` and `L_w = K_v` for `v ∈ T`, in the exact
local-norm form used by Lemma VII.6.4. -/
structure SISetup
    (p : ℕ) (K L : Type u)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] where
  M : Type u
  fieldM : Field M
  numberFieldM : NumberField M
  algebraLM : Algebra L M
  algebraKM : Algebra K M
  scalarTower : IsScalarTower K L M
  finiteDimensionalLM : FiniteDimensional L M
  isGaloisLM : IsGalois L M
  abelianGaloisKM : IsAbelianGalois K M
  S : Finset (NumberFieldPlace K)
  r : ℕ
  t : ℕ
  degreeKL : Module.finrank K L = p ^ r
  cardS : S.card = r + t
  containsInfinite : ContainsAllPlaces K S
  containsDivisors : ∀ v : NumberFieldPlace K,
    normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S
  containsClassGenerators : CIGenera K S
  exponentL : ∀ sigma : Gal(L/K), sigma ^ p = 1
  exponentM : ∀ sigma : Gal(M/K), sigma ^ p = 1
  unramifiedMOutside : ∀ Q : FinitePrime M,
    (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
      Algebra.IsUnramifiedAt (OK K) Q.asIdeal
  unramifiedLOutside : ∀ Q : FinitePrime L,
    (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
      Algebra.IsUnramifiedAt (OK K) Q.asIdeal
  containsSRoots : ContainsPthRoots K M p S
  generatedSRoots : SPthRoots K M p S
  frobeniusBasisCard : ∀ (T : Finset (FinitePrime K)),
    FrobeniusBasis (K := K) (L := L) (M := M)
      p exponentM S T → T.card = t
  selectedPlacesLocally : ∀ (T : Finset (FinitePrime K)),
    FrobeniusBasis (K := K) (L := L) (M := M)
      p exponentM S T → SelectedLocallyTrivial K L T

namespace SISetup

variable {p : ℕ} {K L : Type u}
  [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

attribute [local instance]
  fieldM numberFieldM algebraLM algebraKM scalarTower
  finiteDimensionalLM isGaloisLM abelianGaloisKM

/-- Lemmas VII.6.2--VII.6.10 and the subgroup identity VII.6.5 complete
the second inequality for a field tower carrying the exact Kummer setup
introduced in the source. -/
theorem secondInequality
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (D : SISetup p K L) :
    SecondInequalityAt K L := by
  classical
  have hbasis : HasFrobeniusBasis
      (K := K) (L := L) (M := D.M) p D.exponentM D.S :=
    completionRestrictionStatement p hp K L D.M hroots D.exponentM D.S
      D.unramifiedMOutside
  rw [frobenius_basis] at hbasis
  obtain ⟨T, hT⟩ := hbasis
  have hTcopy := hT
  rcases hTcopy with
    ⟨i, fi, indexPrime, w, b, hindex, hDisjoint, hunder, hbasis, hcompat⟩
  have hsurjective : Function.Surjective
      (obviousMap K p D.S T hDisjoint) :=
    kummerPairingStatement p K L D.M hp hroots D.exponentM D.S
      D.containsDivisors D.unramifiedMOutside D.containsSRoots
      D.generatedSRoots T hDisjoint hT
  have hintersection :
      (principalIntersection K p D.S T).index =
        p ^ (D.S.card + T.card) :=
    intersectionPowerStatement p K hp hroots D.S T D.containsInfinite
      D.containsDivisors D.containsClassGenerators hDisjoint hsurjective
  have htotal :
      (ideleSubgroup K p D.S T).relIndex
          (idelesAtPlaces (K := K) (L := K)
            (combinedPlaces K D.S T)) =
        p ^ (2 * D.S.card) :=
    localIndexStatement p K hp hroots D.S T D.containsInfinite
      D.containsDivisors hDisjoint
  have hENorm : ideleSubgroup K p D.S T ≤
      ideleNormSubgroup (K := K) (L := L) :=
    localBridgesStatement p K L D.exponentL D.S T D.containsInfinite
      (D.selectedPlacesLocally T hT) D.unramifiedLOutside
  let E := ideleSubgroup K p D.S T
  let I := idelesAtPlaces (K := K) (L := K)
    (combinedPlaces K D.S T)
  let C := principalIdeles (OK K) K
  let N := ideleNormSubgroup (K := K) (L := L)
  have hEI : E ≤ I := by
    intro x hx P hP
    change (Sum.inl (P.under (OK K)) : NumberFieldPlace K) ∉
      combinedPlaces K D.S T at hP
    rw [finite_prime_self K P] at hP
    exact hx.2.2 P
      (fun hPS ↦ hP (Finset.mem_union_left _ hPS))
      (fun hPT ↦ hP (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨P, hPT, rfl⟩)))
  have hSI : idelesAtPlaces (K := K) (L := K) D.S ≤ I := by
    intro x hx P hP
    apply hx P
    intro hPS
    apply hP
    exact Finset.mem_union_left _ hPS
  have htopS : C ⊔ idelesAtPlaces (K := K) (L := K) D.S = ⊤ :=
    Towers.CField.BLoc.fractionalIdealPrime
      K D.S D.containsInfinite D.containsClassGenerators
  have htop : I ⊔ C = ⊤ := by
    rw [sup_comm]
    apply top_unique
    rw [← htopS]
    exact sup_le_sup le_rfl hSI
  have hindexProduct := subgroup_relIndex I E C hEI
  have hintersectionTransport :=
    principal_intersection_rel K p D.S T
  change (E ⊔ C).relIndex (I ⊔ C) *
      (E ⊓ C).relIndex (I ⊓ C) = E.relIndex I at hindexProduct
  rw [htop, Subgroup.relIndex_top_right,
    hintersectionTransport, hintersection, htotal] at hindexProduct
  have hTcard : T.card = D.t := D.frobeniusBasisCard T hT
  have hScard : D.S.card = D.r + D.t := D.cardS
  have hexponents :
      2 * D.S.card = D.r + (D.S.card + T.card) := by
    omega
  have hpowerProduct :
      p ^ D.r * p ^ (D.S.card + T.card) = p ^ (2 * D.S.card) := by
    rw [← pow_add, hexponents]
  have hprincipalEIndex : (C ⊔ E).index = p ^ D.r := by
    rw [sup_comm]
    apply Nat.mul_right_cancel (pow_pos hp.pos _)
    exact hindexProduct.trans hpowerProduct.symm
  have hprincipalENorm : C ⊔ E ≤ C ⊔ N :=
    sup_le_sup le_rfl hENorm
  have hnormIndexDvd : (C ⊔ N).index ∣ p ^ D.r := by
    rw [← hprincipalEIndex]
    exact Subgroup.index_dvd_of_le hprincipalENorm
  have hnormIndexPos : 0 < (C ⊔ N).index :=
    Nat.pos_of_dvd_of_pos hnormIndexDvd (pow_pos hp.pos D.r)
  have hcardEq :=
    nat_principal_index K L
  have hquotientCardNe : Nat.card (IdeleNormQuotient K L) ≠ 0 := by
    rw [hcardEq]
    exact hnormIndexPos.ne'
  letI : Finite (IdeleNormQuotient K L) :=
    Nat.finite_of_card_ne_zero hquotientCardNe
  refine ⟨inferInstance, ?_⟩
  rw [hcardEq, D.degreeKL]
  exact hnormIndexDvd

end SISetup

end

end Towers.CField.KNIndex
