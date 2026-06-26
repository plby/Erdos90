import Towers.NumberTheory.Locals.NumberFieldFormula
import Towers.ClassField.IdeleCohomology.NormInvariants
import Towers.ClassField.KummerNormIndex.FiniteLift
import Towers.ClassField.KummerNormIndex.PlaceValue
import Towers.ClassField.KummerNormIndex.PowerIndex

/-!
# Chapter VII, Section 6, Lemma 6.6

For Milne's concrete subgroup `E`, the index in the restricted idèles
`I_(S ∪ T)` is `p^(2 |S|)`.  The proof separates the genuinely local input
from the global idèle bookkeeping.  A coordinate map from `I_(S ∪ T)` to
the product of the local `p`th-power quotients is proved surjective, with
kernel exactly `E`.  The normalized product formula then multiplies the
local index identities from Proposition 6.8.
-/

namespace Towers.CField.KNIndex

open Filter IsDedekindDomain NumberField
open scoped BigOperators RestrictedProduct
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- The multiplicative group of the completion belonging to a finite or
infinite number-field place. -/
abbrev placeUnits
    (K : Type u) [Field K] [NumberField K] :
    NumberFieldPlace K → Type u
  | .inl P => (P.adicCompletion K)ˣ
  | .inr v => v.Completionˣ

noncomputable local instance placeUnitsCommGroup
    (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) : CommGroup (placeUnits K v) := by
  cases v <;> infer_instance

/-- Evaluation of an actual idèle at either kind of number-field place. -/
noncomputable def coordinateHom
    (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) :
    IdeleGroup (OK K) K →* placeUnits K v := by
  cases v with
  | inl P =>
      exact
        { toFun := fun a => a.2.1 P
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
  | inr v =>
      exact
        { toFun := fun a => MulEquiv.piUnits a.1 v
          map_one' := congrFun (map_one (MulEquiv.piUnits :
            (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))) v
          map_mul' := fun a b => congrFun (map_mul (MulEquiv.piUnits :
            (InfiniteAdeleRing K)ˣ ≃* ((w : InfinitePlace K) → w.Completionˣ))
              a.1 b.1) v }

@[simp]
theorem coordinateHom_inl
    (K : Type u) [Field K] [NumberField K]
    (P : FinitePrime K) (a : IdeleGroup (OK K) K) :
    coordinateHom K (Sum.inl P) a = a.2.1 P := by
  rfl

@[simp]
theorem coordinateHom_inr
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K) (a : IdeleGroup (OK K) K) :
    coordinateHom K (Sum.inr v) a = MulEquiv.piUnits a.1 v := by
  rfl

/-- The product over `v ∈ S` of the actual local power-class groups. -/
abbrev localPowerClasses
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K)) :=
  ∀ v : S, placeUnits K v.1 ⧸
    pthPowerSubgroup p (placeUnits K v.1)

/-- The literal finite set `S ∪ T` of places, with the finite primes in
`T` inserted into the full place type. -/
noncomputable def combinedPlaces
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)) :
    Finset (NumberFieldPlace K) := by
  classical
  exact S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K))

/-- The coordinate power-class map on `I_(S ∪ T)`. -/
noncomputable def localPowerClass
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S T : Finset (NumberFieldPlace K)) :
    idelesAtPlaces (K := K) (L := K) T →*
      localPowerClasses K p S where
  toFun a v := QuotientGroup.mk'
    (pthPowerSubgroup p (placeUnits K v.1))
    (coordinateHom K v.1 a.1)
  map_one' := by
    funext v
    change QuotientGroup.mk'
      (pthPowerSubgroup p (placeUnits K v.1))
        (coordinateHom K v.1 (1 : IdeleGroup (OK K) K)) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    funext v
    change QuotientGroup.mk'
      (pthPowerSubgroup p (placeUnits K v.1))
        (coordinateHom K v.1 (a.1 * b.1)) =
      QuotientGroup.mk'
        (pthPowerSubgroup p (placeUnits K v.1))
          (coordinateHom K v.1 a.1) *
      QuotientGroup.mk'
        (pthPowerSubgroup p (placeUnits K v.1))
          (coordinateHom K v.1 b.1)
    rw [map_mul, map_mul]

/-- `E` has the unit condition required to lie in `I_(S ∪ T)`. -/
theorem idele_ideles_places
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K)) :
    ideleSubgroup K p S T ≤
      idelesAtPlaces (K := K) (L := K)
        (combinedPlaces K S T) := by
  classical
  change ideleSubgroup K p S T ≤
    idelesAtPlaces (K := K) (L := K)
      (S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K)))
  intro a ha P hP
  apply ha.2.2 P
  · intro hPS
    exact hP (Finset.mem_union_left _ hPS)
  · intro hPT
    apply hP
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨P, hPT, rfl⟩

private theorem places_in_finite
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) :
    Set.Finite {P : FinitePrime K |
      (Sum.inl P : NumberFieldPlace K) ∈ S} := by
  apply Set.Finite.of_finite_image
      (f := fun P : FinitePrime K ↦ (Sum.inl P : NumberFieldPlace K))
  · apply S.finite_toSet.subset
    rintro _ ⟨P, hP, rfl⟩
    exact hP
  · exact Set.injOn_of_injective Sum.inl_injective

private theorem finite_prime_self
    (K : Type u) [Field K] [NumberField K] (P : FinitePrime K) :
    P.under (OK K) = P := by
  apply HeightOneSpectrum.ext
  ext x
  simp [Ideal.under_def]

set_option synthInstance.maxHeartbeats 300000 in
-- The chosen representatives live in dependent finite and infinite
-- completion groups, which makes elaboration of the restricted product
-- substantially more expensive than the underlying argument.
set_option maxHeartbeats 2000000 in
/-- The local power-class map is onto: finitely many prescribed coordinates
can be inserted into an idèle, with coordinate one everywhere else. -/
theorem local_class_surjective
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K)) :
    Function.Surjective
      (localPowerClass K p S (combinedPlaces K S T)) := by
  classical
  intro y
  have hRepresentative : ∀ v : S, ∃ x : placeUnits K v.1,
      QuotientGroup.mk' (pthPowerSubgroup p (placeUnits K v.1)) x = y v :=
    fun v ↦ (QuotientGroup.mk'_surjective
      (pthPowerSubgroup p (placeUnits K v.1))) (y v)
  choose representative hRepresentative using hRepresentative
  let finiteCoordinates : ∀ P : FinitePrime K, (P.adicCompletion K)ˣ :=
    fun P ↦ if hP : (Sum.inl P : NumberFieldPlace K) ∈ S then
      representative ⟨Sum.inl P, hP⟩ else 1
  let infiniteCoordinates : ∀ v : InfinitePlace K, v.Completionˣ :=
    fun v ↦ if hv : (Sum.inr v : NumberFieldPlace K) ∈ S then
      representative ⟨Sum.inr v, hv⟩ else 1
  have hRestricted : ∀ᶠ P in Filter.cofinite,
      finiteCoordinates P ∈ IdeleUnitSubgroup (OK K) K P := by
    rw [Filter.eventually_cofinite]
    refine (places_in_finite K S).subset ?_
    intro P hPnotUnit
    by_contra hPS
    apply hPnotUnit
    have hPnotS : (Sum.inl P : NumberFieldPlace K) ∉ S := by
      simpa only [Set.mem_setOf_eq] using hPS
    simp only [finiteCoordinates, dif_neg hPnotS]
    exact (IdeleUnitSubgroup (OK K) K P).one_mem
  let finiteIdele : FiniteIdeles (OK K) K :=
    RestrictedProduct.mk finiteCoordinates hRestricted
  let idele : IdeleGroup (OK K) K :=
    (MulEquiv.piUnits.symm infiniteCoordinates, finiteIdele)
  have hidele : idele ∈ idelesAtPlaces (K := K) (L := K)
      (combinedPlaces K S T) := by
    change idele ∈ idelesAtPlaces (K := K) (L := K)
      (S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K)))
    intro P hPT
    change (Sum.inl (P.under (OK K)) : NumberFieldPlace K) ∉
      S ∪ T.image (fun Q ↦ (Sum.inl Q : NumberFieldPlace K)) at hPT
    rw [finite_prime_self K P] at hPT
    by_cases hPS : (Sum.inl P : NumberFieldPlace K) ∈ S
    · exact (hPT (Finset.mem_union_left _ hPS)).elim
    · change finiteCoordinates P ∈ IdeleUnitSubgroup (OK K) K P
      simp only [finiteCoordinates, dif_neg hPS]
      exact (IdeleUnitSubgroup (OK K) K P).one_mem
  refine ⟨⟨idele, hidele⟩, ?_⟩
  funext v
  rcases v with ⟨v, hv⟩
  cases v with
  | inl P =>
      change QuotientGroup.mk'
        (pthPowerSubgroup p ((P.adicCompletion K)ˣ))
          (finiteCoordinates P) = y ⟨Sum.inl P, hv⟩
      simpa only [finiteCoordinates, dif_pos hv] using
        hRepresentative ⟨Sum.inl P, hv⟩
  | inr v =>
      change QuotientGroup.mk'
        (pthPowerSubgroup p v.Completionˣ)
          (MulEquiv.piUnits (MulEquiv.piUnits.symm infiniteCoordinates) v) =
            y ⟨Sum.inr v, hv⟩
      rw [MulEquiv.apply_symm_apply]
      simpa only [infiniteCoordinates, dif_pos hv] using
        hRepresentative ⟨Sum.inr v, hv⟩

set_option synthInstance.maxHeartbeats 300000 in
-- Equality of the kernel and the dependent-coordinate subgroup again
-- requires unfolding both finite and infinite completion group structures.
set_option maxHeartbeats 2000000 in
/-- The kernel of the power-class map is exactly `E`, viewed as a subgroup of
`I_(S ∪ T)`. -/
theorem local_class_ker
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K)) :
    (localPowerClass K p S
      (combinedPlaces K S T)).ker =
      (ideleSubgroup K p S T).subgroupOf
        (idelesAtPlaces (K := K) (L := K)
          (combinedPlaces K S T)) := by
  classical
  change (localPowerClass K p S
      (S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K)))).ker =
    (ideleSubgroup K p S T).subgroupOf
      (idelesAtPlaces (K := K) (L := K)
        (S ∪ T.image (fun P ↦ (Sum.inl P : NumberFieldPlace K))))
  ext a
  constructor
  · intro ha
    have hPower : ∀ v : S,
        coordinateHom K v.1 a.1 ∈
          pthPowerSubgroup p (placeUnits K v.1) := by
      intro v
      apply (QuotientGroup.eq_one_iff _).mp
      have hv := congrFun ha v
      change QuotientGroup.mk'
        (pthPowerSubgroup p (placeUnits K v.1))
          (coordinateHom K v.1 a.1) = 1 at hv
      exact hv
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact hPower ⟨Sum.inr v, hv⟩
    · intro P hP
      exact hPower ⟨Sum.inl P, hP⟩
    · intro P hPS hPT
      apply a.2 P
      change (Sum.inl (P.under (OK K)) : NumberFieldPlace K) ∉
        S ∪ T.image (fun Q ↦ (Sum.inl Q : NumberFieldPlace K))
      rw [finite_prime_self K P]
      intro hPST
      rcases Finset.mem_union.mp hPST with hPST | hPST
      · exact hPS hPST
      · rcases Finset.mem_image.mp hPST with ⟨Q, hQT, hQP⟩
        exact hPT ((Sum.inl_injective hQP) ▸ hQT)
  · intro ha
    funext v
    change QuotientGroup.mk'
      (pthPowerSubgroup p (placeUnits K v.1))
        (coordinateHom K v.1 a.1) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rcases v with ⟨v, hv⟩
    cases v with
    | inl P => exact ha.2.1 P hv
    | inr v => exact ha.1 v hv

/-- The idèle index is purely the product of the local power-subgroup
indices.  This is the global bookkeeping part of Lemma 6.6. -/
theorem rel_index_indices
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K)) :
    (ideleSubgroup K p S T).relIndex
        (idelesAtPlaces (K := K) (L := K)
          (combinedPlaces K S T)) =
      ∏ v : S,
        (pthPowerSubgroup p (placeUnits K v.1)).index := by
  classical
  let I := idelesAtPlaces (K := K) (L := K)
    (combinedPlaces K S T)
  let f := localPowerClass K p S
    (combinedPlaces K S T)
  have hf : Function.Surjective f :=
    local_class_surjective K p S T
  have hker : f.ker = (ideleSubgroup K p S T).subgroupOf I :=
    local_class_ker K p S T
  calc
    (ideleSubgroup K p S T).relIndex I =
        ((ideleSubgroup K p S T).subgroupOf I).index := rfl
    _ = f.ker.index := congrArg Subgroup.index hker.symm
    _ = Nat.card f.range := Subgroup.index_ker f
    _ = Nat.card (localPowerClasses K p S) := by
      rw [MonoidHom.range_eq_top.mpr hf]
      simp
    _ = ∏ v : S, Nat.card
        (placeUnits K v.1 ⧸
          pthPowerSubgroup p (placeUnits K v.1)) := Nat.card_pi
    _ = ∏ v : S,
        (pthPowerSubgroup p (placeUnits K v.1)).index := by
      apply Finset.prod_congr rfl
      intro v _
      rfl

/-- The precise local input still missing uniformly for arbitrary number
field completions.  It is Proposition 6.8 in the form used in the printed
proof.  The archimedean cases are proved in `PowerIndex`; the remaining
content is the nonarchimedean local power-index theorem and its transport to
the canonical completions. -/
def LocalIndexBridge : Prop :=
  ∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
    p.Prime → (primitiveRoots p K).Nonempty →
    ∀ v : NumberFieldPlace K,
      ((pthPowerSubgroup p (placeUnits K v)).index : ℝ) *
          normalizedPlaceValue K v (p : K) = (p : ℝ) ^ 2

/-- Since `S` contains every infinite place and every finite place at which
`|p|_v ≠ 1`, the product over `S` is the full normalized product formula. -/
theorem prod_normalized_place
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (S : Finset (NumberFieldPlace K))
    (hInfinite : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (hDividing : ∀ v : NumberFieldPlace K,
      normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) :
    ∏ v : S, normalizedPlaceValue K v.1 (p : K) = 1 := by
  classical
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hRight : S.toRight = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    simpa only [Finset.mem_toRight] using hInfinite v
  have hFiniteSupport : Function.mulSupport
      (fun P : FinitePrime K ↦
        (FinitePlace.equivHeightOneSpectrum.symm P) (p : K)) ⊆
        (S.toLeft : Set (FinitePrime K)) := by
    intro P hP
    apply Finset.mem_toLeft.mpr
    apply hDividing (Sum.inl P)
    exact hP
  rw [show (∏ v : S, normalizedPlaceValue K v.1 (p : K)) =
      ∏ v ∈ S, normalizedPlaceValue K v (p : K) by
        exact Finset.prod_coe_sort
          S (fun v ↦ normalizedPlaceValue K v (p : K))]
  rw [Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight, hRight]
  change (∏ P ∈ S.toLeft,
      (FinitePlace.equivHeightOneSpectrum.symm P) (p : K)) *
      (∏ v : InfinitePlace K, v.1 (p : K) ^ v.mult) = 1
  rw [mul_comm]
  rw [← finprod_eq_prod_of_mulSupport_subset _ hFiniteSupport]
  change (∏ v : InfinitePlace K, v.1 (p : K) ^ v.mult) *
      (∏ᶠ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
        (FinitePlace.equivHeightOneSpectrum.symm P) (p : K)) = 1
  simpa only [← finprod_comp_equiv
    (FinitePlace.equivHeightOneSpectrum (K := K)).symm] using
      (number_product_formula hpK)

/-- Multiplying Proposition 6.8 over `S` and applying the actual number-field
product formula gives the numerical local-index product in Lemma 6.6. -/
theorem prod_local_indices
    (hlocal : LocalIndexBridge.{u})
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K))
    (hInfinite : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (hDividing : ∀ v : NumberFieldPlace K,
      normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) :
    (∏ v : S,
      (pthPowerSubgroup p (placeUnits K v.1)).index) =
        p ^ (2 * S.card) := by
  classical
  have hValues := prod_normalized_place
    p K hp S hInfinite hDividing
  have hReal :
      ((∏ v : S,
        (pthPowerSubgroup p (placeUnits K v.1)).index : ℕ) : ℝ) *
          ∏ v : S, normalizedPlaceValue K v.1 (p : K) =
        ((p : ℝ) ^ 2) ^ S.card := by
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
    calc
      _ = ∏ v : S, (p : ℝ) ^ 2 := by
        apply Finset.prod_congr rfl
        intro v _
        exact hlocal p K hp hroots v.1
      _ = ((p : ℝ) ^ 2) ^ S.card := by simp
  rw [hValues, mul_one, ← pow_mul] at hReal
  exact_mod_cast hReal

/-- Lemma 6.6 from the local power-index identity of Proposition 6.8. -/
theorem place_units_index
    (hlocal : LocalIndexBridge.{u}) :
    (∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
          p.Prime → (primitiveRoots p K).Nonempty →
          ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
            (∀ v : InfinitePlace K,
              (Sum.inr v : NumberFieldPlace K) ∈ S) →
            (∀ v : NumberFieldPlace K,
              normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) →
            (∀ P : FinitePrime K, P ∈ T →
              (Sum.inl P : NumberFieldPlace K) ∉ S) →
            (ideleSubgroup K p S T).relIndex
                (idelesAtPlaces (K := K) (L := K)
                  (combinedPlaces K S T)) =
              p ^ (2 * S.card)) := by
  intro p K _ _ hp hroots S T hInfinite hDividing _hDisjoint
  rw [rel_index_indices]
  exact prod_local_indices hlocal p K hp hroots S
    hInfinite hDividing

end

end Towers.CField.KNIndex
