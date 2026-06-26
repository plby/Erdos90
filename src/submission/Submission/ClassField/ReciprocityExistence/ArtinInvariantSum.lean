import Submission.ClassField.ReciprocityExistence.ArtinCoordinates
import Submission.ClassField.ReciprocityExistence.LocalFinprod
import Submission.ClassField.ReciprocityExistence.LawStatements

/-!
# Summing the character values of a full Artin product

After Proposition III.3.6 identifies every local invariant with the
corresponding local character value, the right square of Lemma VII.8.5 is a
finite-product calculation.  This file performs that calculation for the
finite and infinite places simultaneously.
-/

namespace Submission.CField.RExist

open Function Set
open IsDedekindDomain NumberField
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.Recip
open scoped RestrictedProduct

noncomputable section

universe u v w

/-- A finitely supported sum over a sum type splits into the sums over its
two kinds of indices. -/
theorem finsum_type_support
    {ι κ : Type u} {B : Type v} [AddCommGroup B]
    (f : ι ⊕ κ → B) (hf : HasFiniteSupport f) :
    (∑ᶠ i, f i) = (∑ᶠ i, f (.inl i)) + ∑ᶠ k, f (.inr k) := by
  rw [← finsum_mem_univ f, ← range_inl_union_range_inr]
  rw [finsum_mem_union']
  · rw [finsum_mem_range Sum.inl_injective,
      finsum_mem_range Sum.inr_injective]
  · rw [Set.disjoint_range_iff]
    exact fun _ _ => Sum.inl_ne_inr
  · exact hf.inter_of_right _
  · exact hf.inter_of_right _

/-- A character turns a finite product into the finite sum of its values. -/
theorem finsum_character_finprod
    {ι : Type u} {A : Type v} {B : Type w}
    [CommGroup A] [AddCommGroup B]
    (chi : Additive A →+ B) (f : ι → A)
    (hf : HasFiniteMulSupport f) :
    (∑ᶠ i, chi (Additive.ofMul (f i))) =
      chi (Additive.ofMul (∏ᶠ i, f i)) := by
  let chiMul : A →* Multiplicative B := chi.toMultiplicative
  have hmap := chiMul.map_finprod hf
  apply Multiplicative.ofAdd.injective
  change Multiplicative.ofAdd
      (∑ᶠ i, chi (Additive.ofMul (f i))) =
    Multiplicative.ofAdd
      (chi (Additive.ofMul (∏ᶠ i, f i)))
  rw [finsum_eq_sum_of_support_subset
    (fun i => chi (Additive.ofMul (f i)))]
  · change (∏ i ∈ hf.toFinset, chiMul (f i)) =
      chiMul (∏ᶠ i, f i)
    rw [hmap]
    exact (finprod_eq_prod_of_mulSupport_subset
      (fun i => chiMul (f i)) (by
        intro i hi
        apply hf.mem_toFinset.2
        change f i ≠ 1
        intro hone
        apply hi
        change chiMul (f i) = 1
        rw [hone]
        exact map_one chiMul)).symm
  · intro i hi
    apply hf.mem_toFinset.2
    change f i ≠ 1
    intro hone
    apply hi
    change chi (Additive.ofMul (f i)) = 0
    rw [hone]
    exact map_zero chi

open scoped Classical in
/-- If each coordinate invariant is the character value of the selected
local Artin factor, their total sum is the character value of the complete
finite-and-infinite Artin product. -/
theorem direct_character_artin
    {K A : Type u} [Field K] [NumberField K] [CommGroup A]
    {C : NumberFieldPlace K → Type v} [∀ place, AddCommGroup (C place)]
    {B : Type w} [AddCommGroup B]
    (D : FAProduc K A)
    (chi : Additive A →+ B)
    (x : IdeleGroup (RingOfIntegers K) K)
    (inv : ∀ place, C place →+ B)
    (b : DirectSum (NumberFieldPlace K) C)
    (hfinite : ∀ P,
      inv (.inl P) (b (.inl P)) =
        chi (Additive.ofMul (D.finite.localHom P (x.2.1 P))))
    (hinfinite : ∀ v,
      inv (.inr v) (b (.inr v)) =
        chi (Additive.ofMul
          (D.infinite v (MulEquiv.piUnits x.1 v)))) :
    DirectSum.toAddMonoid inv b =
      chi (Additive.ofMul (D.artin x)) := by
  classical
  rw [direct_monoid_finsum]
  have hsupport : HasFiniteSupport (fun place => inv place (b place)) := by
    apply b.support.finite_toSet.subset
    intro place hplace
    exact (DFinsupp.mem_support_toFun b place).2 (by
      intro hb
      apply hplace
      change inv place (b place) = 0
      rw [hb, map_zero])
  rw [finsum_type_support _ hsupport]
  rw [show (fun P => inv (.inl P) (b (.inl P))) =
      (fun P => chi (Additive.ofMul
        (D.finite.localHom P (x.2.1 P)))) by
    funext P
    exact hfinite P]
  rw [show (fun v => inv (.inr v) (b (.inr v))) =
      (fun v => chi (Additive.ofMul
        (D.infinite v (MulEquiv.piUnits x.1 v)))) by
    funext v
    exact hinfinite v]
  rw [finsum_character_finprod chi
      (fun P => D.finite.localHom P (x.2.1 P))
      (D.finite.finite_mulSupport _ x.2),
    finsum_character_finprod chi
      (fun v => D.infinite v (MulEquiv.piUnits x.1 v))
      (Set.toFinite _),
    finprod_eq_prod_of_fintype
      (fun v : InfinitePlace K =>
        D.infinite v (MulEquiv.piUnits x.1 v))]
  rw [← map_add]
  apply congrArg chi
  change
    Additive.ofMul ((∏ᶠ P : HeightOneSpectrum (RingOfIntegers K),
        D.finite.localHom P (x.2.1 P)) *
      (∏ v : InfinitePlace K,
        D.infinite v (MulEquiv.piUnits x.1 v))) =
      Additive.ofMul (D.artin x)
  apply congrArg Additive.ofMul
  rw [D.artin_apply]
  exact mul_comm _ _

open scoped Classical in
/-- The right square of Lemma VII.8.5 follows from its finite- and
infinite-place coordinate formulas once the global Artin homomorphism has
been identified with the corresponding product of local Artin maps. -/
theorem cup_comparison_artin
    {K A : Type u} [Field K] [NumberField K] [CommGroup A]
    {C : NumberFieldPlace K → Type v} [∀ place, AddCommGroup (C place)]
    (D : FAProduc K A)
    (artin : IdeleGroup (RingOfIntegers K) K →* A)
    (ideleCup : CharacterModule (Additive A) →
      Additive (IdeleGroup (RingOfIntegers K) K) →+
        DirectSum (NumberFieldPlace K) C)
    (inv : ∀ place, C place →+ LocalInvariant)
    (hartin : artin = D.artin)
    (hfinite : ∀ chi a P,
      inv (.inl P)
          (ideleCup chi (Additive.ofMul a) (.inl P)) =
        chi (Additive.ofMul (D.finite.localHom P (a.2.1 P))))
    (hinfinite : ∀ chi a v,
      inv (.inr v)
          (ideleCup chi (Additive.ofMul a) (.inr v)) =
        chi (Additive.ofMul
          (D.infinite v (MulEquiv.piUnits a.1 v)))) :
    CupInvariantComparison artin ideleCup
      (DirectSum.toAddMonoid inv) := by
  intro chi a
  rw [hartin]
  exact direct_character_artin D chi a inv
    (ideleCup chi (Additive.ofMul a))
    (hfinite chi a) (hinfinite chi a)

end

end Submission.CField.RExist
