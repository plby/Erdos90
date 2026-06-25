import Towers.ClassField.KummerNormIndex.PrincipalIdeleHom
import Towers.ClassField.KummerNormIndex.LocalCriterionIdeles

/-!
# The reverse inclusion in Lemma VII.6.7

Lemma 6.9 supplies the local-unit surjection for the previously selected set
`T`.  Proposition 6.10 then says that a principal idèle lying in Milne's
subgroup `E` is a global `p`th power.  Its root is again an `S ∪ T`-unit,
which proves the deferred reverse inclusion.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.CField.Ideles
open Towers.CField.NIndex
open Towers.NumberTheory.Milne

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- A principal idèle in `E` is the `p`th power of an `S ∪ T`-unit. -/
theorem intersectionPowerBridge :
    IntersectionPowerBridge.{u} := by
  classical
  intro p K _ _ hp hroots S T hInfinite hDividing hClass hDisjoint
    hsurjective x hx
  have hxE :
      principalIdele (OK K) K (x : Kˣ) ∈ ideleSubgroup K p S T := by
    exact hx
  have hLocal : ∀ v : NumberFieldPlace K, v ∈ S →
      nthPowerPlace K p (x : Kˣ) v := by
    intro v hv
    cases v with
    | inl P =>
        obtain ⟨y, hy⟩ := hxE.2.1 P hv
        refine ⟨(y : P.adicCompletion K), ?_⟩
        have hy' := congrArg Units.val hy
        simpa only [finiteCoordinate, principal_idele_finite,
          Units.val_pow_eq_pow_val, Units.coe_map] using hy'
    | inr v =>
        obtain ⟨y, hy⟩ := hxE.1 v hv
        refine ⟨(y : v.Completion), ?_⟩
        have hy' := congrArg Units.val hy
        simpa only [infiniteCoordinate, principal_idele_infinite,
          Units.val_pow_eq_pow_val, Units.coe_map] using hy'
  have hUnit : nthPlaceOutside K (x : Kˣ) S T := by
    intro P hP
    exact x.property P hP
  obtain ⟨y, hy⟩ := criterionIdelesStatement p K hroots S T
    hInfinite hDividing hClass hDisjoint hsurjective (x : Kˣ) hLocal hUnit
  have hyField : (y : K) ^ p = ((x : Kˣ) : K) := congrArg Units.val hy
  let yS : sUnits K S T :=
    ⟨y, fun P hP => by
      apply (pow_eq_one_iff_left hp.ne_zero).mp
      rw [← map_pow, hyField, x.property P hP]⟩
  refine ⟨yS, ?_⟩
  apply Subtype.ext
  exact hy

/-- **Lemma VII.6.7.** -/
theorem intersectionPowerStatement : (∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
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
  principal_idele_intersection
    intersectionPowerBridge

end

end Towers.CField.KNIndex
