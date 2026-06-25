import Towers.ClassField.KummerNormIndex.PlaceUnits
import Towers.ClassField.KummerNormIndex.FinitelyGeneratedPower
import Towers.ClassField.KummerNormIndex.ObviousMap
import Towers.ClassField.NormIndex.FractionalIdealPrime

/-!
# Chapter VII, Section 6, Lemma 6.7

For Milne's subgroup `E`, this file realizes `K× ∩ E` as the pullback of
`E` along the diagonal map from the actual `S ∪ T`-unit group.  The easy
inclusion `U(S ∪ T)^p ⊆ K× ∩ E` is proved directly from the local
coordinates of a principal idèle.

The printed proof postpones the reverse inclusion to Lemma 6.9 and
Proposition 6.10.  We therefore expose precisely that inclusion, and the
separate numerical consequence of the `S`-unit theorem, as bridges.  Neither
bridge assumes the desired index formula.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.HQuotie
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Milne's group `U(S ∪ T)`, with the finite primes of `T` inserted into
the full set of number-field places. -/
abbrev sUnits
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)) :=
  ArithmeticSUnits K (finitePrimePart K (combinedPlaces K S T))

/-- The diagonal map on the actual `S ∪ T`-unit group. -/
noncomputable def principalIdeleHom
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)) :
    sUnits K S T →* IdeleGroup (OK K) K :=
  (principalIdele (OK K) K).comp
    (Set.unit (finitePrimePart K (combinedPlaces K S T)) K).subtype

/-- The literal subgroup `K× ∩ E`, regarded inside `U(S ∪ T)`. -/
def principalIntersection
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K)) : Subgroup (sUnits K S T) :=
  (ideleSubgroup K p S T).comap
    (principalIdeleHom K S T)

/-- Every `p`th power in `U(S ∪ T)` lies in `K× ∩ E`.  This is the
"clearly" inclusion at the start of Milne's proof of Lemma 6.7. -/
theorem sunit_powers_intersection
    (K : Type u) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K)) :
    pthPowerSubgroup p (sUnits K S T) ≤
      principalIntersection K p S T := by
  classical
  rintro x ⟨y, rfl⟩
  change principalIdele (OK K) K (((y ^ p : sUnits K S T) : Kˣ)) ∈
    ideleSubgroup K p S T
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    refine ⟨infiniteCoordinate K
      (principalIdele (OK K) K (y : Kˣ)) v, ?_⟩
    change coordinateHom K (Sum.inr v)
        (principalIdele (OK K) K (y : Kˣ)) ^ p =
      coordinateHom K (Sum.inr v)
        (principalIdele (OK K) K
          (((y ^ p : sUnits K S T) : Kˣ)))
    calc
      _ = coordinateHom K (Sum.inr v)
          ((principalIdele (OK K) K (y : Kˣ)) ^ p) :=
        (map_pow (coordinateHom K (Sum.inr v))
          (principalIdele (OK K) K (y : Kˣ)) p).symm
      _ = coordinateHom K (Sum.inr v)
          (principalIdele (OK K) K ((y : Kˣ) ^ p)) := by
        exact congrArg (coordinateHom K (Sum.inr v))
          (map_pow (principalIdele (OK K) K) (y : Kˣ) p).symm
      _ = _ := rfl
  · intro P hP
    refine ⟨finiteCoordinate K
      (principalIdele (OK K) K (y : Kˣ)) P, ?_⟩
    change coordinateHom K (Sum.inl P)
        (principalIdele (OK K) K (y : Kˣ)) ^ p =
      coordinateHom K (Sum.inl P)
        (principalIdele (OK K) K
          (((y ^ p : sUnits K S T) : Kˣ)))
    calc
      _ = coordinateHom K (Sum.inl P)
          ((principalIdele (OK K) K (y : Kˣ)) ^ p) :=
        (map_pow (coordinateHom K (Sum.inl P))
          (principalIdele (OK K) K (y : Kˣ)) p).symm
      _ = coordinateHom K (Sum.inl P)
          (principalIdele (OK K) K ((y : Kˣ) ^ p)) := by
        exact congrArg (coordinateHom K (Sum.inl P))
          (map_pow (principalIdele (OK K) K) (y : Kˣ) p).symm
      _ = _ := rfl
  · intro P hPS hPT
    change (principalIdele (OK K) K
      (((y ^ p : sUnits K S T) : Kˣ))).2.1 P ∈
        IdeleUnitSubgroup (OK K) K P
    rw [principal_idele_finite]
    apply (place_embedding_subgroup (L := K) P
      (((y ^ p : sUnits K S T) : Kˣ))).2
    apply (y ^ p).property P
    intro hPCombined
    change (Sum.inl P : NumberFieldPlace K) ∈
      combinedPlaces K S T at hPCombined
    change (Sum.inl P : NumberFieldPlace K) ∈
      S ∪ T.image (fun Q ↦ (Sum.inl Q : NumberFieldPlace K)) at hPCombined
    rcases Finset.mem_union.mp hPCombined with hPCombined | hPCombined
    · exact hPS hPCombined
    · rcases Finset.mem_image.mp hPCombined with ⟨Q, hQT, hQP⟩
      exact hPT ((Sum.inl_injective hQP) ▸ hQT)

/-- The `p`-torsion in an `S`-unit group is the group of `p`th roots of
unity in the field.  A root of unity is an `S`-unit because every finite
valuation of it is one. -/
noncomputable def rootsUnityS
    (p : ℕ) (hp : p ≠ 0)
    (K : Type u) [Field K] [NumberField K]
    (R : Set (FinitePrime K)) :
    rootsOfUnity p K ≃*
      (powMonoidHom p : ArithmeticSUnits K R →* ArithmeticSUnits K R).ker where
  toFun z := by
    let x : ArithmeticSUnits K R :=
      ⟨(z : Kˣ), fun P _ ↦ valuation_one_pow
        (P.valuation K) hp
          ((mem_rootsOfUnity' p (z : Kˣ)).mp z.property)⟩
    exact ⟨x, by
      apply Subtype.ext
      exact z.property⟩
  invFun x :=
    ⟨(x.1 : ArithmeticSUnits K R).1, by
      change ((x.1 : ArithmeticSUnits K R).1 : Kˣ) ^ p = 1
      exact congrArg Subtype.val x.property⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The unit-theorem power-index calculation for an arbitrary finite set of
finite primes. -/
theorem sunit_power_index
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (R : Set (FinitePrime K)) (hR : R.Finite) :
    (pthPowerSubgroup p (ArithmeticSUnits K R)).index =
      p ^ (Module.finrank ℤ (Additive (ArithmeticSUnits K R)) + 1) := by
  letI : Group.FG (ArithmeticSUnits K R) :=
    Group.fg_iff_monoid_fg.mpr (s_finitely_generated K R hR)
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨zeta, hzeta⟩ := hroots
  have hkernel : Nat.card
      (powMonoidHom p : ArithmeticSUnits K R →* ArithmeticSUnits K R).ker = p := by
    rw [← Nat.card_congr
      (rootsUnityS p hp.ne_zero K R).toEquiv]
    rw [Nat.card_eq_fintype_card]
    exact ((mem_primitiveRoots hp.pos).mp hzeta).card_rootsOfUnity
  rw [fg_index_formula (ArithmeticSUnits K R) p hp.ne_zero, hkernel, pow_succ]

/-- The finite-prime part of `S ∪ T` is the disjoint union of the finite
part of `S` and `T`. -/
theorem prime_part_combined
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)) :
    finitePrimePart K (combinedPlaces K S T) =
      (S.toLeft : Set (FinitePrime K)) ∪ (T : Set (FinitePrime K)) := by
  classical
  ext P
  simp [finitePrimePart, combinedPlaces]

/-- The numerical `S`-unit theorem input used in the printed proof is
already a consequence of the formalized `S`-unit rank theorem and the
general finitely generated abelian-group power-index formula. -/
theorem sunit_index_combined
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K))
    (hInfinite : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
      (Sum.inl P : NumberFieldPlace K) ∉ S) :
    (pthPowerSubgroup p (sUnits K S T)).index =
      p ^ (S.card + T.card) := by
  classical
  let R : Set (FinitePrime K) :=
    finitePrimePart K (combinedPlaces K S T)
  have hR : R.Finite := by
    rw [show R = (S.toLeft : Set (FinitePrime K)) ∪
        (T : Set (FinitePrime K)) by
      exact prime_part_combined K S T]
    exact S.toLeft.finite_toSet.union T.finite_toSet
  rw [sunit_power_index p K hp hroots R hR]
  congr 1
  have hST : Disjoint S.toLeft T := by
    rw [Finset.disjoint_left]
    intro P hPS hPT
    exact hDisjoint P hPT (Finset.mem_toLeft.mp hPS)
  have hRcard : R.ncard = S.toLeft.card + T.card := by
    rw [show R = (S.toLeft : Set (FinitePrime K)) ∪
        (T : Set (FinitePrime K)) by
      exact prime_part_combined K S T]
    rw [Set.ncard_union_eq (by exact_mod_cast hST)]
    simp
  have hRight : S.toRight = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    exact Finset.mem_toRight.mpr (hInfinite v)
  have hInfiniteCard : S.toRight.card =
      NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K := by
    rw [hRight, Finset.card_univ,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  rw [s_complex_ncard K R hR]
  have hSCard : S.toLeft.card + S.toRight.card = S.card :=
    S.card_toLeft_add_card_toRight
  have hPlaces : 0 < NumberField.InfinitePlace.nrRealPlaces K +
      NumberField.InfinitePlace.nrComplexPlaces K := by
    rw [← NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  omega

/-- The numerical `S`-unit theorem input used in the printed proof:
`[U(S ∪ T) : U(S ∪ T)^p] = p^(|S|+|T|)`.

The hypotheses are exactly the ones used for the count: `K` contains a
primitive `p`th root, `S` contains every infinite place, and `T` is disjoint
from the finite part of `S`. -/
def SIndexBridge : Prop :=
  ∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
    p.Prime → (primitiveRoots p K).Nonempty →
    ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
      (∀ v : InfinitePlace K,
        (Sum.inr v : NumberFieldPlace K) ∈ S) →
      (∀ P : FinitePrime K, P ∈ T →
        (Sum.inl P : NumberFieldPlace K) ∉ S) →
      (pthPowerSubgroup p (sUnits K S T)).index =
        p ^ (S.card + T.card)

/-- The formalized `S`-unit theorem proves the numerical input without any
additional hypothesis. -/
theorem sunitIndexBridge :
    SIndexBridge.{u} := by
  intro p K _ _ hp hroots S T hInfinite hDisjoint
  exact sunit_index_combined p K hp hroots S T
    hInfinite hDisjoint

/-- The second input is exactly the inclusion deferred in the source to
Lemma 6.9 and Proposition 6.10.  Since the printed lemma says "with the
above notation", the hypotheses retain the earlier choice of `S` containing
ideal-class generators and the surjectivity established for the selected
Frobenius-basis set `T` in Lemma 6.9. -/
def IntersectionPowerBridge : Prop :=
  ∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
    p.Prime → (primitiveRoots p K).Nonempty →
    ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
      (∀ v : InfinitePlace K,
        (Sum.inr v : NumberFieldPlace K) ∈ S) →
      (∀ v : NumberFieldPlace K,
        normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) →
      CIGenera K S →
      ∀ (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
        (Sum.inl P : NumberFieldPlace K) ∉ S),
      Function.Surjective (obviousMap K p S T hDisjoint) →
      principalIntersection K p S T ≤
        pthPowerSubgroup p (sUnits K S T)

/-- Lemma 6.7 from the `S`-unit theorem and the reverse inclusion supplied
by Lemma 6.9 and Proposition 6.10. -/
theorem principal_idele_bridges
    (hunit : SIndexBridge.{u})
    (hintersection : IntersectionPowerBridge.{u}) :
    (∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
          p.Prime → (primitiveRoots p K).Nonempty →
          ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
            (∀ v : InfinitePlace K,
              (Sum.inr v : NumberFieldPlace K) ∈ S) →
            (∀ v : NumberFieldPlace K,
              normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) →
            CIGenera K S →
            ∀ (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
              (Sum.inl P : NumberFieldPlace K) ∉ S),
            Function.Surjective (obviousMap K p S T hDisjoint) →
            (principalIntersection K p S T).index =
              p ^ (S.card + T.card)) := by
  intro p K _ _ hp hroots S T hInfinite hDividing hClass hDisjoint
    hsurjective
  have heq : principalIntersection K p S T =
      pthPowerSubgroup p (sUnits K S T) :=
    le_antisymm
      (hintersection p K hp hroots S T hInfinite hDividing hClass
        hDisjoint hsurjective)
      (sunit_powers_intersection K p S T)
  rw [heq]
  exact hunit p K hp hroots S T hInfinite hDisjoint

/-- Lemma 6.7 with only the reverse inclusion left to Lemma 6.9 and
Proposition 6.10, exactly as in the source. -/
theorem principal_idele_intersection
    (hintersection : IntersectionPowerBridge.{u}) :
    (∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
          p.Prime → (primitiveRoots p K).Nonempty →
          ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
            (∀ v : InfinitePlace K,
              (Sum.inr v : NumberFieldPlace K) ∈ S) →
            (∀ v : NumberFieldPlace K,
              normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) →
            CIGenera K S →
            ∀ (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
              (Sum.inl P : NumberFieldPlace K) ∉ S),
            Function.Surjective (obviousMap K p S T hDisjoint) →
            (principalIntersection K p S T).index =
              p ^ (S.card + T.card)) :=
  principal_idele_bridges
    sunitIndexBridge hintersection

end

end Towers.CField.KNIndex
