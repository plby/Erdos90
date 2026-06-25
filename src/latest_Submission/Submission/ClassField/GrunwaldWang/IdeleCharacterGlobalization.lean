import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.IntegralDomain
import Submission.NumberTheory.Galois.DecompositionGroup
import Submission.ClassField.Reciprocity.ArtinMapStatements
import Submission.ClassField.GrunwaldWang.GrunwaldWangStatement

/-!
# Globalizing an idele-class character of order three

This file contains the purely global half of the passage from an order-three
idele-class character to a cyclic cubic extension.  It uses only the global
Artin map, idelic reciprocity, and the idelic existence theorem.  No local
inertia comparison is made here.
-/

namespace Submission.CField.GWang

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.Recip
open scoped IsMulCommutative

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- A finite-order continuous circle-valued character has finite image. -/
theorem circle_character_range
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    (chi : A →ₜ* Circle) (hchi : IsOfFinOrder chi) :
    Finite chi.toMonoidHom.range := by
  let n := orderOf chi
  letI : NeZero n := ⟨hchi.orderOf_pos.ne'⟩
  let f : chi.toMonoidHom.range → rootsOfUnity n Circle := fun z ↦
    ⟨toUnits z.1, by
      rw [mem_rootsOfUnity]
      rcases z.2 with ⟨x, hx⟩
      rw [← map_pow, ← hx]
      have hpow : chi ^ n = 1 := by
        dsimp only [n]
        exact pow_orderOf_eq_one chi
      have hxpow : chi x ^ n = 1 := by
        simpa using DFunLike.congr_fun hpow x
      simpa only [map_one] using congrArg toUnits hxpow⟩
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    exact toUnits.injective (congrArg Subtype.val hzw)
  exact Finite.of_injective f hf

/-- The image cardinality of a finite-order continuous circle-valued
character is its order. -/
theorem circle_character_card
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    (chi : A →ₜ* Circle) (hchi : IsOfFinOrder chi) :
    Nat.card chi.toMonoidHom.range = orderOf chi := by
  letI : Finite chi.toMonoidHom.range :=
    circle_character_range chi hchi
  let rangeToComplex : chi.toMonoidHom.range →* ℂ :=
    Circle.coeHom.comp chi.toMonoidHom.range.subtype
  letI : IsCyclic chi.toMonoidHom.range :=
    isCyclic_of_injective_ringHom rangeToComplex
      (Circle.coe_injective.comp chi.toMonoidHom.range.subtype_injective)
  obtain ⟨g, hg⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard
      (α := chi.toMonoidHom.range)
  rcases g.2 with ⟨x, hx⟩
  have hleft : Nat.card chi.toMonoidHom.range ∣ orderOf chi := by
    rw [← hg]
    apply orderOf_dvd_of_pow_eq_one
    have hgpow : (g : Circle) ^ orderOf chi = 1 := by
      rw [← hx]
      have hpow : chi ^ orderOf chi = 1 := pow_orderOf_eq_one chi
      simpa only [ContinuousMonoidHom.pow_apply,
        ContinuousMonoidHom.coe_one, Pi.one_apply] using
        DFunLike.congr_fun hpow x
    apply Subtype.ext
    exact hgpow
  have hright : orderOf chi ∣ Nat.card chi.toMonoidHom.range := by
    apply orderOf_dvd_of_pow_eq_one
    apply DFunLike.ext _ _
    intro x
    have hxpow := congrArg Subtype.val
      (pow_card_eq_one'
        (x := (⟨chi x, ⟨x, rfl⟩⟩ : chi.toMonoidHom.range)))
    change chi x ^ Nat.card chi.toMonoidHom.range = (1 : Circle) at hxpow
    simpa only [ContinuousMonoidHom.pow_apply,
      ContinuousMonoidHom.coe_one, Pi.one_apply] using hxpow
  exact Nat.dvd_antisymm hleft hright

/-- If a character is obtained by following a homomorphism with an injective
circle-valued character, its order is the cardinality of the first
homomorphism's image. -/
theorem circle_character_compatible
    {A G : Type*} [CommGroup A] [TopologicalSpace A] [Group G]
    (chi : A →ₜ* Circle) (hchi : IsOfFinOrder chi)
    (f : A →* G) (c : G →* Circle) (hc : Function.Injective c)
    (hcompat : ∀ x, c (f x) = chi x) :
    orderOf chi = Nat.card f.range := by
  let rangeMap : f.range →* chi.toMonoidHom.range := {
    toFun := fun z : f.range => ⟨c z.1, by
      show c z.1 ∈ chi.toMonoidHom.range
      rcases z.2 with ⟨x, hx⟩
      exact ⟨x, (hcompat x).symm.trans (congrArg c hx)⟩⟩
    map_one' := by
      apply Subtype.ext
      exact map_one c
    map_mul' := fun (x y : f.range) => by
      apply Subtype.ext
      exact map_mul c x.1 y.1 }
  have hrangeMap : Function.Bijective rangeMap := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hc (congrArg Subtype.val hxy)
    · intro y
      rcases y.2 with ⟨x, hx⟩
      refine ⟨⟨f x, ⟨x, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      exact (hcompat x).trans hx
  let e : f.range ≃* chi.toMonoidHom.range :=
    MulEquiv.ofBijective rangeMap hrangeMap
  calc
    orderOf chi = Nat.card chi.toMonoidHom.range :=
      (circle_character_card chi hchi).symm
    _ = Nat.card f.range := Nat.card_congr e.symm.toEquiv

/-- The image of a finite-order idèle-class character is finite. -/
theorem idele_character_range
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi) :
    Finite chi.toMonoidHom.range := by
  let n := orderOf chi
  letI : NeZero n := ⟨hchi.orderOf_pos.ne'⟩
  let f : chi.toMonoidHom.range → rootsOfUnity n Circle := fun z ↦
    ⟨toUnits z.1, by
      rw [mem_rootsOfUnity]
      rcases z.2 with ⟨x, hx⟩
      rw [← map_pow, ← hx]
      have hpow : chi ^ n = 1 := by
        dsimp only [n]
        exact pow_orderOf_eq_one chi
      have hxpow : chi x ^ n = 1 := by
        simpa using DFunLike.congr_fun hpow x
      simpa only [map_one] using congrArg toUnits hxpow⟩
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    exact toUnits.injective (congrArg Subtype.val hzw)
  exact Finite.of_injective f hf

/-- The image cardinality of a finite-order idèle-class character is exactly
the order of the character. -/
theorem character_range_card
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi) :
    Nat.card chi.toMonoidHom.range = orderOf chi := by
  letI : Finite chi.toMonoidHom.range :=
    idele_character_range chi hchi
  let rangeToComplex : chi.toMonoidHom.range →* ℂ :=
    Circle.coeHom.comp chi.toMonoidHom.range.subtype
  letI : IsCyclic chi.toMonoidHom.range :=
    isCyclic_of_injective_ringHom rangeToComplex
      (Circle.coe_injective.comp chi.toMonoidHom.range.subtype_injective)
  obtain ⟨g, hg⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard
      (α := chi.toMonoidHom.range)
  rcases g.2 with ⟨x, hx⟩
  have hleft : Nat.card chi.toMonoidHom.range ∣ orderOf chi := by
    rw [← hg]
    apply orderOf_dvd_of_pow_eq_one
    have hgpow : (g : Circle) ^ orderOf chi = 1 := by
      rw [← hx]
      have hpow : chi ^ orderOf chi = 1 := pow_orderOf_eq_one chi
      simpa only [ContinuousMonoidHom.pow_apply,
        ContinuousMonoidHom.coe_one, Pi.one_apply] using
        DFunLike.congr_fun hpow x
    apply Subtype.ext
    exact hgpow
  have hright : orderOf chi ∣ Nat.card chi.toMonoidHom.range := by
    apply orderOf_dvd_of_pow_eq_one
    apply DFunLike.ext _ _
    intro x
    have hxpow := congrArg Subtype.val
      (pow_card_eq_one'
        (x := (⟨chi x, ⟨x, rfl⟩⟩ : chi.toMonoidHom.range)))
    change chi x ^ Nat.card chi.toMonoidHom.range = (1 : Circle) at hxpow
    simpa only [ContinuousMonoidHom.pow_apply,
      ContinuousMonoidHom.coe_one, Pi.one_apply] using hxpow
  exact Nat.dvd_antisymm hleft hright

/-- The kernel of a finite-order idèle-class character is open. -/
theorem character_ker_open
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi) :
    IsOpen (chi.toMonoidHom.ker :
      Set (IdeleClassGroup (NumberField.RingOfIntegers K) K)) := by
  letI : Finite chi.toMonoidHom.range :=
    idele_character_range chi hchi
  let rangeCharacter :
      IdeleClassGroup (NumberField.RingOfIntegers K) K →ₜ*
        chi.toMonoidHom.range :=
    { toMonoidHom := chi.toMonoidHom.rangeRestrict
      continuous_toFun := chi.continuous_toFun.subtype_mk _ }
  have hopen : IsOpen ({1} : Set chi.toMonoidHom.range) :=
    isOpen_discrete {1}
  have hpre := hopen.preimage rangeCharacter.continuous_toFun
  convert hpre using 1
  ext x
  change chi x = 1 ↔ rangeCharacter x = 1
  constructor
  · intro hx
    apply Subtype.ext
    exact hx
  · intro hx
    exact congrArg Subtype.val hx

/-- The kernel of a finite-order idèle-class character has finite index. -/
theorem character_ker_index
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi) :
    chi.toMonoidHom.ker.FiniteIndex := by
  letI : Finite chi.toMonoidHom.range :=
    idele_character_range chi hchi
  infer_instance

private theorem idele_class_character
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3)
    (x : IdeleClassGroup (NumberField.RingOfIntegers K) K) :
    chi x ^ 3 = 1 := by
  have hpow : chi ^ 3 = 1 := by
    rw [← hchi]
    exact pow_orderOf_eq_one chi
  simpa using DFunLike.congr_fun hpow x

/-- The image of an order-three circle-valued character is finite. -/
theorem idele_character_finite
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3) :
    Finite chi.toMonoidHom.range := by
  let f : chi.toMonoidHom.range → rootsOfUnity 3 Circle := fun z ↦
    ⟨toUnits z.1, by
      rw [mem_rootsOfUnity]
      rcases z.2 with ⟨x, hx⟩
      rw [← map_pow, ← hx]
      have hp : chi.toMonoidHom x ^ 3 = 1 :=
        idele_class_character chi hchi x
      rw [hp, map_one]⟩
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    exact toUnits.injective (congrArg Subtype.val hzw)
  exact Finite.of_injective f hf

/-- An order-three idele-class character has an image of exactly three
elements. -/
theorem idele_character_three
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3) :
    Nat.card chi.toMonoidHom.range = 3 := by
  letI : Finite chi.toMonoidHom.range :=
    idele_character_finite chi hchi
  let f : chi.toMonoidHom.range → rootsOfUnity 3 Circle := fun z ↦
    ⟨toUnits z.1, by
      rw [mem_rootsOfUnity]
      rcases z.2 with ⟨x, hx⟩
      rw [← map_pow, ← hx]
      have hp : chi.toMonoidHom x ^ 3 = 1 :=
        idele_class_character chi hchi x
      rw [hp, map_one]⟩
  have hf : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    exact toUnits.injective (congrArg Subtype.val hzw)
  have hle : Nat.card chi.toMonoidHom.range ≤ 3 := by
    calc
      Nat.card chi.toMonoidHom.range ≤ Nat.card (rootsOfUnity 3 Circle) :=
        Nat.card_le_card_of_injective f hf
      _ = 3 := HasEnoughRootsOfUnity.natCard_rootsOfUnity Circle 3
  have hne : chi ≠ 1 := by
    intro h
    have hone : orderOf chi = 1 := orderOf_eq_one_iff.mpr h
    omega
  obtain ⟨x, hx⟩ : ∃ x, chi x ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    ext y
    simpa using h y
  let y : chi.toMonoidHom.range := ⟨chi x, ⟨x, rfl⟩⟩
  have hyne : y ≠ 1 := by
    intro hy
    apply hx
    exact congrArg Subtype.val hy
  have hypow : y ^ 3 = 1 := by
    apply Subtype.ext
    exact idele_class_character chi hchi x
  have hyorder : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one hypow
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact (hyne (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hdiv : 3 ∣ Nat.card chi.toMonoidHom.range := by
    rw [← hyorder]
    exact orderOf_dvd_natCard y
  rcases hdiv with ⟨m, hm⟩
  have hpos : 0 < Nat.card chi.toMonoidHom.range := Nat.card_pos
  omega

/-- The kernel of an order-three idele-class character is open. -/
theorem idele_character_open
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3) :
    IsOpen (chi.toMonoidHom.ker :
      Set (IdeleClassGroup (NumberField.RingOfIntegers K) K)) := by
  letI : Finite chi.toMonoidHom.range :=
    idele_character_finite chi hchi
  let rangeCharacter :
      IdeleClassGroup (NumberField.RingOfIntegers K) K →ₜ*
        chi.toMonoidHom.range :=
    { toMonoidHom := chi.toMonoidHom.rangeRestrict
      continuous_toFun := chi.continuous_toFun.subtype_mk _ }
  have hopen : IsOpen ({1} : Set chi.toMonoidHom.range) :=
    isOpen_discrete {1}
  have hpre := hopen.preimage rangeCharacter.continuous_toFun
  convert hpre using 1
  ext x
  change chi x = 1 ↔ rangeCharacter x = 1
  constructor
  · intro hx
    apply Subtype.ext
    exact hx
  · intro hx
    exact congrArg Subtype.val hx

/-- The kernel of an order-three idele-class character has finite index. -/
theorem idele_character_index
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3) :
    chi.toMonoidHom.ker.FiniteIndex := by
  letI : Finite chi.toMonoidHom.range :=
    idele_character_finite chi hchi
  infer_instance

set_option maxHeartbeats 2000000 in
-- Factoring the finite Artin map unfolds nested idele quotient instances.
private theorem range_character_reciprocity
    (chi : IdeleClassCharacter K)
    (L : FASubext K) [NumberField L.1]
    (hL : ideleClassSubgroup L = chi.toMonoidHom.ker)
    (artin : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hreciprocity :
      FiniteReciprocityLaw (NumberField.RingOfIntegers K) K Gal(L.1/K)
        ((localAbelianRestriction L).comp artin)
        (ideleNormSubgroup (K := K) (L := L.1))) :
    ∃ finiteRangeCharacter : Gal(L.1/K) →* chi.toMonoidHom.range,
      Function.Bijective finiteRangeCharacter ∧
        finiteRangeCharacter.comp ((localAbelianRestriction L).comp artin) =
          chi.toMonoidHom.rangeRestrict.comp
            (QuotientGroup.mk'
              (principalIdeles (NumberField.RingOfIntegers K) K)) := by
  let R := NumberField.RingOfIntegers K
  let artinL : IdeleGroup R K →* Gal(L.1/K) :=
    (localAbelianRestriction L).comp artin
  let classMap : IdeleGroup R K →*
      IdeleClassGroup (NumberField.RingOfIntegers K) K :=
    QuotientGroup.mk' (principalIdeles R K)
  let target : IdeleGroup R K →* chi.toMonoidHom.range :=
    chi.toMonoidHom.rangeRestrict.comp classMap
  have htarget_surjective : Function.Surjective target :=
    chi.toMonoidHom.rangeRestrict_surjective.comp
      (QuotientGroup.mk'_surjective (principalIdeles R K))
  have hprincipal_target : principalIdeles R K ≤ target.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change chi (classMap a) = 1
    have hclass : classMap a = 1 := by
      change (a : IdeleGroup R K ⧸ principalIdeles R K) = 1
      exact (QuotientGroup.eq_one_iff a).mpr ha
    calc
      chi (classMap a) = chi 1 := congrArg chi hclass
      _ = 1 := chi.map_one
  have hnorm_target :
      ideleNormSubgroup (K := K) (L := L.1) ≤ target.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change chi (classMap a) = 1
    have hclass : classMap a ∈ chi.toMonoidHom.ker := by
      rw [← hL]
      exact ⟨a, ha, rfl⟩
    exact hclass
  have hartinL_ker_le : artinL.ker ≤ target.ker := by
    intro a ha
    apply (sup_le hprincipal_target hnorm_target)
    rw [hreciprocity.2]
    exact ha
  let finiteRangeCharacter : Gal(L.1/K) →* chi.toMonoidHom.range :=
    artinL.liftOfSurjective hreciprocity.1
      ⟨target, hartinL_ker_le⟩
  have hfiniteRange_comp : finiteRangeCharacter.comp artinL = target := by
    exact artinL.liftOfRightInverse_comp
      (Function.surjInv hreciprocity.1)
      (Function.rightInverse_surjInv hreciprocity.1)
      ⟨target, hartinL_ker_le⟩
  have hfiniteRange_surjective :
      Function.Surjective finiteRangeCharacter := by
    intro z
    obtain ⟨a, ha⟩ := htarget_surjective z
    refine ⟨artinL a, ?_⟩
    rw [← ha]
    exact DFunLike.congr_fun hfiniteRange_comp a
  have hfiniteRange_injective :
      Function.Injective finiteRangeCharacter := by
    apply (injective_iff_map_eq_one finiteRangeCharacter).2
    intro sigma hsigma
    obtain ⟨a, rfl⟩ := hreciprocity.1 sigma
    have htarget_one : target a = 1 := by
      rw [← DFunLike.congr_fun hfiniteRange_comp a]
      exact hsigma
    have hchi_one : chi (classMap a) = 1 :=
      congrArg Subtype.val htarget_one
    have hclass : classMap a ∈ chi.toMonoidHom.ker := hchi_one
    rw [← hL] at hclass
    rcases hclass with ⟨n, hn, hna⟩
    have hp : a / n ∈ principalIdeles R K :=
      QuotientGroup.eq_iff_div_mem.mp hna.symm
    have ha_sup :
        a ∈ principalIdeles R K ⊔
          ideleNormSubgroup (K := K) (L := L.1) :=
      Subgroup.mem_sup.mpr
        ⟨a / n, hp, n, hn, div_mul_cancel a n⟩
    have ha_ker : a ∈ artinL.ker := by
      rw [← hreciprocity.2]
      exact ha_sup
    exact ha_ker
  exact ⟨finiteRangeCharacter,
    ⟨hfiniteRange_injective, hfiniteRange_surjective⟩,
    hfiniteRange_comp⟩

private structure CubicArtinData
    (chi : IdeleClassCharacter K) where
  extension : FASubext K
  globalArtinMap :
    IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K
  global_artin_continuous : Continuous globalArtinMap
  global_artin_map : GlobalArtin globalArtinMap
  finiteRangeCharacter :
    Gal(extension.1/K) →* chi.toMonoidHom.range
  range_character_bijective :
    Function.Bijective finiteRangeCharacter
  range_character_comp :
    finiteRangeCharacter.comp
        ((localAbelianRestriction extension).comp globalArtinMap) =
      chi.toMonoidHom.rangeRestrict.comp
        (QuotientGroup.mk'
          (principalIdeles (NumberField.RingOfIntegers K) K))

set_option synthInstance.maxHeartbeats 1000000 in
-- The finite-layer global reciprocity predicate has nested completion instances.
set_option maxHeartbeats 3000000 in
-- Applying all three global CFT statements simultaneously is typeclass-heavy.
private theorem cubic_artin_data
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3)
    (hV52 : GlobalArtinProposition (K := K))
    (hV53 : IdeleReciprocityLaw (K := K))
    (hV55 : IdeleExistenceTheorem (K := K)) :
    Nonempty (CubicArtinData chi) := by
  let N := chi.toMonoidHom.ker
  have hNopen : IsOpen (N :
      Set (IdeleClassGroup (NumberField.RingOfIntegers K) K)) :=
    idele_character_open chi hchi
  have hNindex : N.FiniteIndex :=
    idele_character_index chi hchi
  obtain ⟨L, hL, _⟩ := hV55 N hNopen hNindex
  letI : NumberField L.1 := NumberField.of_module_finite K L.1
  obtain ⟨artin, hartin, _⟩ := hV52
  obtain ⟨_, hreciprocity⟩ := hV53 artin hartin
  obtain ⟨finiteRangeCharacter, hbijective, hcomp⟩ :=
    range_character_reciprocity
      chi L (by simpa [N] using hL) artin (hreciprocity L)
  exact ⟨⟨L, artin, hartin.1, hartin.2, finiteRangeCharacter,
    hbijective, hcomp⟩⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- The finite-layer global reciprocity predicate has nested completion instances.
set_option maxHeartbeats 3000000 in
-- Applying all three global CFT statements simultaneously is typeclass-heavy.
private theorem character_artin_data
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi)
    (hV52 : GlobalArtinProposition (K := K))
    (hV53 : IdeleReciprocityLaw (K := K))
    (hV55 : IdeleExistenceTheorem (K := K)) :
    Nonempty (CubicArtinData chi) := by
  let N := chi.toMonoidHom.ker
  have hNopen : IsOpen (N :
      Set (IdeleClassGroup (NumberField.RingOfIntegers K) K)) :=
    character_ker_open chi hchi
  have hNindex : N.FiniteIndex :=
    character_ker_index chi hchi
  obtain ⟨L, hL, _⟩ := hV55 N hNopen hNindex
  letI : NumberField L.1 := NumberField.of_module_finite K L.1
  obtain ⟨artin, hartin, _⟩ := hV52
  obtain ⟨_, hreciprocity⟩ := hV53 artin hartin
  obtain ⟨finiteRangeCharacter, hbijective, hcomp⟩ :=
    range_character_reciprocity
      chi L (by simpa [N] using hL) artin (hreciprocity L)
  exact ⟨⟨L, artin, hartin.1, hartin.2, finiteRangeCharacter,
    hbijective, hcomp⟩⟩

/-- The global data cut out by an order-three idele-class character.  The
finite character is faithful, and the absolute character is its pullback
along restriction to the displayed cubic subextension. -/
structure CCGlobal (chi : IdeleClassCharacter K) where
  extension : FASubext K
  degree_eq_three : Module.finrank K extension.1 = 3
  cyclic : IsCyclic Gal(extension.1/K)
  globalArtinMap :
    IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K
  global_artin_continuous : Continuous globalArtinMap
  global_artin_map : GlobalArtin globalArtinMap
  finiteCharacter : Gal(extension.1/K) →* Circle
  finiteCharacter_injective : Function.Injective finiteCharacter
  absoluteCharacter : LocalAbsoluteGalois K →ₜ* Circle
  absoluteCharacter_apply (sigma : LocalAbsoluteGalois K) :
    absoluteCharacter sigma =
      finiteCharacter
        (AlgEquiv.restrictNormalHom
          extension.finiteIntermediateField sigma)
  artin_compatibility
      (a : IdeleGroup (NumberField.RingOfIntegers K) K) :
    finiteCharacter
        (localAbelianRestriction extension (globalArtinMap a)) =
      chi (QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers K) K) a)

/-- Global class-field data cut out by an arbitrary finite-order idèle-class
character.  Its cyclic degree is exactly the order of the character. -/
structure OCGlobala
    (chi : IdeleClassCharacter K) where
  extension : FASubext K
  degree_eq_order : Module.finrank K extension.1 = orderOf chi
  cyclic : IsCyclic Gal(extension.1/K)
  globalArtinMap :
    IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K
  global_artin_continuous : Continuous globalArtinMap
  global_artin_map : GlobalArtin globalArtinMap
  finiteCharacter : Gal(extension.1/K) →* Circle
  finiteCharacter_injective : Function.Injective finiteCharacter
  absoluteCharacter : LocalAbsoluteGalois K →ₜ* Circle
  absoluteCharacter_apply (sigma : LocalAbsoluteGalois K) :
    absoluteCharacter sigma =
      finiteCharacter
        (AlgEquiv.restrictNormalHom
          extension.finiteIntermediateField sigma)
  artin_compatibility
      (a : IdeleGroup (NumberField.RingOfIntegers K) K) :
    finiteCharacter
        (localAbelianRestriction extension (globalArtinMap a)) =
      chi (QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers K) K) a)

/-- The absolute character factors through abelianization and restriction to
the cubic subextension. -/
theorem CCGlobal.absolutec_abeliani
    {chi : IdeleClassCharacter K}
    (data : CCGlobal chi)
    (sigma : LocalAbsoluteGalois K) :
    data.absoluteCharacter sigma =
      data.finiteCharacter
        (localAbelianRestriction data.extension
          (localAbelianizationMap K sigma)) := by
  rw [data.absoluteCharacter_apply,
    abelian_restriction_quotient]

/-- Strong absolute-Galois compatibility with global reciprocity: every
global Artin symbol has an absolute-Galois lift, and the absolute character
of any displayed lift is exactly the original idele-class character value. -/
theorem CCGlobal.exists_liftg_artin
    {chi : IdeleClassCharacter K}
    (data : CCGlobal chi)
    (a : IdeleGroup (NumberField.RingOfIntegers K) K) :
    ∃ sigma : LocalAbsoluteGalois K,
      localAbelianizationMap K sigma = data.globalArtinMap a ∧
        data.absoluteCharacter sigma =
          chi (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers K) K) a) := by
  obtain ⟨sigma, hsigma⟩ :=
    QuotientGroup.mk'_surjective
      (Subgroup.topologicalClosure
        (commutator (LocalAbsoluteGalois K)))
      (data.globalArtinMap a)
  change localAbelianizationMap K sigma = data.globalArtinMap a at hsigma
  refine ⟨sigma, hsigma, ?_⟩
  rw [data.absolutec_abeliani, hsigma]
  exact data.artin_compatibility a

/-- At a finite place, the finite character supplied by globalization pulls
back along the local Artin map to the local character prescribed before
globalization. -/
theorem CCGlobal.exists_place_artin
    {chi : IdeleClassCharacter K}
    (data : CCGlobal chi)
    [NumberField data.extension.1]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := data.extension.1) P)
    (chiP : LocalCharacter K (.inl P))
    (hchiP : CharacterRestrictsTo K chi (.inl P) chiP) :
    ∃ phiP : (P.adicCompletion K)ˣ →* Gal(data.extension.1/K),
      LayerLocalArtin data.extension P Q phiP ∧
        ∀ x : (P.adicCompletion K)ˣ,
          data.finiteCharacter (phiP x) = chiP x := by
  obtain ⟨phiP, hphiP, hglobal⟩ :=
    data.global_artin_map.1 data.extension P Q
  refine ⟨phiP, hphiP, fun x => ?_⟩
  rw [← hglobal x, data.artin_compatibility]
  exact hchiP x

/-- At a finite place, arbitrary finite-order globalization pulls back along
the finite-layer local Artin map to the prescribed local character. -/
theorem OCGlobala.exists_place_artin
    {chi : IdeleClassCharacter K}
    (data : OCGlobala chi)
    [NumberField data.extension.1]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := data.extension.1) P)
    (chiP : LocalCharacter K (.inl P))
    (hchiP : CharacterRestrictsTo K chi (.inl P) chiP) :
    ∃ phiP : (P.adicCompletion K)ˣ →* Gal(data.extension.1/K),
      LayerLocalArtin data.extension P Q phiP ∧
        ∀ x : (P.adicCompletion K)ˣ,
          data.finiteCharacter (phiP x) = chiP x := by
  obtain ⟨phiP, hphiP, hglobal⟩ :=
    data.global_artin_map.1 data.extension P Q
  refine ⟨phiP, hphiP, fun x => ?_⟩
  rw [← hglobal x, data.artin_compatibility]
  exact hchiP x

/-- At an infinite place, arbitrary finite-order globalization pulls back
along the archimedean local Artin map to the prescribed local character. -/
theorem OCGlobala.exists_place_artia
    {chi : IdeleClassCharacter K}
    (data : OCGlobala chi)
    [NumberField data.extension.1]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := data.extension.1) v)
    (chi_v : LocalCharacter K (.inr v))
    (hchi_v : CharacterRestrictsTo K chi (.inr v) chi_v) :
    ∃ phi_v : v.1.Completionˣ →* Gal(data.extension.1/K),
      InfiniteLayerArtin data.extension v w phi_v ∧
        ∀ x : v.1.Completionˣ,
          data.finiteCharacter (phi_v x) = chi_v x := by
  obtain ⟨phi_v, hphi_v, hglobal⟩ :=
    data.global_artin_map.2 data.extension v w
  refine ⟨phi_v, hphi_v, fun x => ?_⟩
  rw [← hglobal x, data.artin_compatibility]
  exact hchi_v x

set_option synthInstance.maxHeartbeats 300000 in
-- The local reciprocity datum contains several completion transports.
set_option maxHeartbeats 2000000 in
/-- A finite-layer local Artin map has image exactly the decomposition group
at the completion appearing in its defining reciprocity datum. -/
theorem artin_range_decomposition
    (L : FASubext K) [NumberField L.1]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P)
    (phi : (P.adicCompletion K)ˣ →* Gal(L.1/K))
    (hphi : LayerLocalArtin L P Q phi) :
    ∃ (w : AbsoluteValue L.1 ℝ)
      (_hwv : AbsoluteValue.LiesOver w (FinitePlace.mk P).val),
      w.IsEquiv
          (FinitePlace.mk (upperPrime (K := K) (L := L.1) P Q)).val ∧
        phi.range = absoluteValueDecomposition
          (FinitePlace.mk P).val w := by
  rcases hphi with ⟨w, hwv, hwq, e, hformula, _hnormalized⟩
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w v) := ⟨hwv⟩
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  let baseUnitsEquiv : (P.adicCompletion K)ˣ ≃* v.Completionˣ :=
    Units.mapEquiv
      (placeCompletionAdic P).symm.toMulEquiv
  let localRec : v.Completionˣ →* Gal(w.Completion/v.Completion) :=
    e.toMonoidHom.comp
      (QuotientGroup.mk' (normSubgroup v.Completion w.Completion))
  have hlocalRec : Function.Surjective localRec := by
    intro sigma
    obtain ⟨q, rfl⟩ := e.surjective sigma
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (normSubgroup v.Completion w.Completion) q
    exact ⟨y, rfl⟩
  let transport :=
    (decompositionCompletionExtension v w).symm
  let localMap : (P.adicCompletion K)ˣ →*
      absoluteValueDecomposition v w :=
    transport.toMonoidHom.comp
      (localRec.comp baseUnitsEquiv.toMonoidHom)
  have hlocalMap : Function.Surjective localMap :=
    transport.surjective.comp
      (hlocalRec.comp baseUnitsEquiv.surjective)
  have hformula' (x : (P.adicCompletion K)ˣ) :
      phi x = (localMap x : Gal(L.1/K)) := by
    exact hformula x
  refine ⟨w, hwv, hwq, ?_⟩
  ext sigma
  constructor
  · rintro ⟨x, rfl⟩
    rw [hformula' x]
    exact (localMap x).property
  · intro hsigma
    obtain ⟨x, hx⟩ := hlocalMap
      (⟨sigma, hsigma⟩ : absoluteValueDecomposition v w)
    exact ⟨x, (hformula' x).trans (congrArg Subtype.val hx)⟩

omit [NumberField K] in
/-- An infinite-layer local Artin map has image exactly the corresponding
archimedean decomposition group. -/
theorem infinite_artin_decomposition
    (L : FASubext K) [NumberField L.1]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L.1) v)
    (phi : v.1.Completionˣ →* Gal(L.1/K))
    (hphi : InfiniteLayerArtin L v w phi) :
    phi.range = absoluteValueDecomposition v.1 w.1.1 := by
  rcases hphi with ⟨e, hformula⟩
  let localMap : v.1.Completionˣ →*
      absoluteValueDecomposition v.1 w.1.1 :=
    e.toMonoidHom.comp
      (QuotientGroup.mk'
        (infiniteCompletionNorm (K := K) (L := L.1) v w).range)
  have hlocalMap : Function.Surjective localMap :=
    e.surjective.comp
      (QuotientGroup.mk'_surjective
        (infiniteCompletionNorm (K := K) (L := L.1) v w).range)
  have hformula' (x : v.1.Completionˣ) :
      phi x = (localMap x : Gal(L.1/K)) := hformula x
  ext sigma
  constructor
  · rintro ⟨x, rfl⟩
    rw [hformula' x]
    exact (localMap x).property
  · intro hsigma
    obtain ⟨x, hx⟩ := hlocalMap
      (⟨sigma, hsigma⟩ : absoluteValueDecomposition v.1 w.1.1)
    exact ⟨x, (hformula' x).trans (congrArg Subtype.val hx)⟩

/-- If the prescribed local character is nontrivial on valuation units, then
the local Artin symbols of those units fill the whole cubic Galois group.
This is the group-theoretic half of the usual units-to-inertia comparison;
identifying this range with integral inertia is a separate local statement. -/
theorem CCGlobal.exists_place_charu
    {chi : IdeleClassCharacter K}
    (data : CCGlobal chi)
    [NumberField data.extension.1]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := data.extension.1) P)
    (chiP : LocalCharacter K (.inl P))
    (hchiP : CharacterRestrictsTo K chi (.inl P) chiP)
    (U : Subgroup (P.adicCompletion K)ˣ)
    (hnontrivial : ∃ u : U, chiP (u : (P.adicCompletion K)ˣ) ≠ 1) :
    ∃ phiP : (P.adicCompletion K)ˣ →* Gal(data.extension.1/K),
      LayerLocalArtin data.extension P Q phiP ∧
        U.map phiP = ⊤ ∧
        ∀ x : (P.adicCompletion K)ˣ,
          data.finiteCharacter (phiP x) = chiP x := by
  obtain ⟨phiP, hphiP, hcompat⟩ :=
    data.exists_place_artin P Q chiP hchiP
  have hcard : Nat.card Gal(data.extension.1/K) = 3 :=
    (IsGalois.card_aut_eq_finrank K data.extension.1).trans
      data.degree_eq_three
  letI : Fact (Nat.card Gal(data.extension.1/K)).Prime :=
    ⟨hcard ▸ Nat.prime_three⟩
  have hunitRange : U.map phiP = ⊤ := by
    rcases (U.map phiP).eq_bot_or_eq_top_of_prime_card with hbot | htop
    · obtain ⟨u, hu⟩ := hnontrivial
      have hmem : phiP (u : (P.adicCompletion K)ˣ) ∈
          U.map phiP :=
        ⟨u, u.property, rfl⟩
      rw [hbot] at hmem
      have hphiOne : phiP (u : (P.adicCompletion K)ˣ) = 1 :=
        Subgroup.mem_bot.mp hmem
      exfalso
      apply hu
      rw [← hcompat (u : (P.adicCompletion K)ˣ), hphiOne, map_one]
    · exact htop
  exact ⟨phiP, hphiP, hunitRange, hcompat⟩

private noncomputable def artinDataCharacter
    (chi : IdeleClassCharacter K) (data : CubicArtinData chi) :
    Gal(data.extension.1/K) →* Circle :=
  chi.toMonoidHom.range.subtype.comp data.finiteRangeCharacter

private theorem artin_character_injective
    (chi : IdeleClassCharacter K) (data : CubicArtinData chi) :
    Function.Injective (artinDataCharacter chi data) :=
  chi.toMonoidHom.range.subtype_injective.comp
    data.range_character_bijective.1

private theorem artin_gal_three
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3)
    (data : CubicArtinData chi) :
    Nat.card Gal(data.extension.1/K) = 3 := by
  let e : Gal(data.extension.1/K) ≃* chi.toMonoidHom.range :=
    MulEquiv.ofBijective data.finiteRangeCharacter
      data.range_character_bijective
  calc
    Nat.card Gal(data.extension.1/K) = Nat.card chi.toMonoidHom.range :=
      Nat.card_congr e.toEquiv
    _ = 3 := idele_character_three chi hchi

private theorem artin_data_three
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3)
    (data : CubicArtinData chi) :
    Module.finrank K data.extension.1 = 3 :=
  (IsGalois.card_aut_eq_finrank K data.extension.1).symm.trans
    (artin_gal_three chi hchi data)

private theorem artin_data_cyclic
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3)
    (data : CubicArtinData chi) :
    IsCyclic Gal(data.extension.1/K) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isCyclic_of_prime_card
    (artin_gal_three chi hchi data)

private theorem artin_gal_order
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi)
    (data : CubicArtinData chi) :
    Nat.card Gal(data.extension.1/K) = orderOf chi := by
  let e : Gal(data.extension.1/K) ≃* chi.toMonoidHom.range :=
    MulEquiv.ofBijective data.finiteRangeCharacter
      data.range_character_bijective
  calc
    Nat.card Gal(data.extension.1/K) = Nat.card chi.toMonoidHom.range :=
      Nat.card_congr e.toEquiv
    _ = orderOf chi :=
      character_range_card chi hchi

private theorem artin_data_order
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi)
    (data : CubicArtinData chi) :
    Module.finrank K data.extension.1 = orderOf chi :=
  (IsGalois.card_aut_eq_finrank K data.extension.1).symm.trans
    (artin_gal_order chi hchi data)

private theorem artin_cyclic_order
    (chi : IdeleClassCharacter K)
    (data : CubicArtinData chi) :
    IsCyclic Gal(data.extension.1/K) :=
  isCyclic_of_injective_ringHom
    (Circle.coeHom.comp (artinDataCharacter chi data))
    (Circle.coe_injective.comp
      (artin_character_injective chi data))

private noncomputable def artinContinuousCharacter
    (chi : IdeleClassCharacter K) (data : CubicArtinData chi) :
    Gal(data.extension.1/K) →ₜ* Circle :=
  { toMonoidHom := artinDataCharacter chi data
    continuous_toFun := continuous_of_discreteTopology }

set_option maxHeartbeats 2000000 in
-- Krull restriction continuity unfolds the finite intermediate-field topology.
private noncomputable def artinAbsoluteRestriction
    (chi : IdeleClassCharacter K) (data : CubicArtinData chi) :
    LocalAbsoluteGalois K →ₜ* Gal(data.extension.1/K) :=
  { toMonoidHom := AlgEquiv.restrictNormalHom
      data.extension.finiteIntermediateField
    continuous_toFun := InfiniteGalois.restrictNormalHom_continuous
      (k := K) (K := SeparableClosure K)
      data.extension.finiteIntermediateField }

private noncomputable def artinAbsoluteCharacter
    (chi : IdeleClassCharacter K) (data : CubicArtinData chi) :
    LocalAbsoluteGalois K →ₜ* Circle :=
  (artinContinuousCharacter chi data).comp
    (artinAbsoluteRestriction chi data)

private theorem artin_absolute_character
    (chi : IdeleClassCharacter K) (data : CubicArtinData chi)
    (sigma : LocalAbsoluteGalois K) :
    artinAbsoluteCharacter chi data sigma =
      artinDataCharacter chi data
        (AlgEquiv.restrictNormalHom
          data.extension.finiteIntermediateField sigma) := by
  rfl

private theorem artin_data_compatibility
    (chi : IdeleClassCharacter K) (data : CubicArtinData chi)
    (a : IdeleGroup (NumberField.RingOfIntegers K) K) :
    artinDataCharacter chi data
        (localAbelianRestriction data.extension (data.globalArtinMap a)) =
      chi (QuotientGroup.mk'
        (principalIdeles (NumberField.RingOfIntegers K) K) a) := by
  exact congrArg Subtype.val
    (DFunLike.congr_fun data.range_character_comp a)

private noncomputable def cubicGlobalizationArtin
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3)
    (data : CubicArtinData chi) :
    CCGlobal chi where
  extension := data.extension
  degree_eq_three := artin_data_three chi hchi data
  cyclic := artin_data_cyclic chi hchi data
  globalArtinMap := data.globalArtinMap
  global_artin_continuous := data.global_artin_continuous
  global_artin_map := data.global_artin_map
  finiteCharacter := artinDataCharacter chi data
  finiteCharacter_injective := artin_character_injective chi data
  absoluteCharacter := artinAbsoluteCharacter chi data
  absoluteCharacter_apply := artin_absolute_character chi data
  artin_compatibility := artin_data_compatibility chi data

/-- Build the arbitrary finite-order globalization from the common Artin
data used by the cubic construction. -/
private noncomputable def globalizationArtinData
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi)
    (data : CubicArtinData chi) :
    OCGlobala chi where
  extension := data.extension
  degree_eq_order := artin_data_order chi hchi data
  cyclic := artin_cyclic_order chi data
  globalArtinMap := data.globalArtinMap
  global_artin_continuous := data.global_artin_continuous
  global_artin_map := data.global_artin_map
  finiteCharacter := artinDataCharacter chi data
  finiteCharacter_injective := artin_character_injective chi data
  absoluteCharacter := artinAbsoluteCharacter chi data
  absoluteCharacter_apply := artin_absolute_character chi data
  artin_compatibility := artin_data_compatibility chi data

set_option synthInstance.maxHeartbeats 1000000 in
-- The chosen global CFT data contains nested finite-layer quotient instances.
set_option maxHeartbeats 3000000 in
/-- V.5.2, V.5.3, and V.5.5 turn an order-three idele-class character into
a cyclic cubic subextension and a continuous absolute Galois character.

The last field of the resulting structure is the exact reciprocity
compatibility: evaluation on the finite restriction of the global Artin
symbol is literally evaluation of the original idele-class character. -/
theorem cubic_character_globalization
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3)
    (hV52 : GlobalArtinProposition (K := K))
    (hV53 : IdeleReciprocityLaw (K := K))
    (hV55 : IdeleExistenceTheorem (K := K)) :
    Nonempty (CCGlobal chi) := by
  obtain ⟨data⟩ :=
    cubic_artin_data chi hchi hV52 hV53 hV55
  exact ⟨cubicGlobalizationArtin chi hchi data⟩

/-- A chosen globalization of an order-three idele-class character. -/
noncomputable def cubicCharacterGlobalization
    (chi : IdeleClassCharacter K) (hchi : orderOf chi = 3)
    (hV52 : GlobalArtinProposition (K := K))
    (hV53 : IdeleReciprocityLaw (K := K))
    (hV55 : IdeleExistenceTheorem (K := K)) :
    CCGlobal chi :=
  Classical.choice
    (cubic_character_globalization chi hchi hV52 hV53 hV55)

set_option synthInstance.maxHeartbeats 1000000 in
-- The chosen global CFT data contains nested finite-layer quotient instances.
set_option maxHeartbeats 3000000 in
/-- V.5.2, V.5.3, and V.5.5 turn any finite-order idèle-class character into
a cyclic extension whose degree is exactly the character order. -/
theorem idele_character_globalization
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi)
    (hV52 : GlobalArtinProposition (K := K))
    (hV53 : IdeleReciprocityLaw (K := K))
    (hV55 : IdeleExistenceTheorem (K := K)) :
    Nonempty (OCGlobala chi) := by
  obtain ⟨data⟩ :=
    character_artin_data chi hchi hV52 hV53 hV55
  exact ⟨globalizationArtinData chi hchi data⟩

/-- A chosen cyclic class field cut out by a finite-order idèle-class
character. -/
noncomputable def ideleCharacterGlobalization
    (chi : IdeleClassCharacter K) (hchi : IsOfFinOrder chi)
    (hV52 : GlobalArtinProposition (K := K))
    (hV53 : IdeleReciprocityLaw (K := K))
    (hV55 : IdeleExistenceTheorem (K := K)) :
    OCGlobala chi :=
  Classical.choice
    (idele_character_globalization chi hchi hV52 hV53 hV55)

end

end Submission.CField.GWang
