import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Atoms.Finite
import Towers.ClassField.NormLimitation.FiniteQuotients

/-!
# Prime-index supergroups in finite abelian quotients

The induction in Theorem VII.9.5 starts with a proper finite-index subgroup
`U` of an abelian group and chooses a subgroup `U₁ ⊇ U` of prime index.
Equivalently, one chooses a maximal proper subgroup of the finite quotient
`C / U`.  Its quotient is a finite simple abelian group, hence has prime
cardinality.  This file records that argument without any idèlic input.
-/

namespace Towers.CField.NLimita

noncomputable section

variable {C : Type*} [CommGroup C]

/-- A coatom in the subgroup lattice of a commutative group has a simple
quotient. -/
private theorem simple_group_coatom
    {G : Type*} [CommGroup G] (H : Subgroup G) (hH : IsCoatom H) :
    IsSimpleGroup (G ⧸ H) := by
  let q := QuotientGroup.mk' H
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective H
  letI : Nontrivial (G ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH.1
  refine
    { eq_bot_or_eq_top_of_normal := ?_ }
  intro N _hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · right
    have hker : q.ker = H := QuotientGroup.ker_mk' H
    have hle : H ≤ N.comap q := by
      intro x hx
      have hxker : x ∈ q.ker := hker.symm ▸ hx
      change q x ∈ N
      rw [show q x = 1 from hxker]
      exact N.one_mem
    have hne : N.comap q ≠ H := by
      intro h
      apply hNbot
      apply Subgroup.comap_injective hq
      simp [h, hker]
    have hlt : H < N.comap q := lt_of_le_of_ne hle hne.symm
    have htop : N.comap q = ⊤ := hH.2 _ hlt
    apply Subgroup.comap_injective hq
    simp [htop]

/-- Every proper finite-index subgroup of a commutative group is contained
in a subgroup of prime index.  The resulting quotient is killed by that
prime, in the exact form needed to apply Lemma VII.9.3. -/
theorem prime_index_supergroup
    (U : Subgroup C) [U.FiniteIndex] (hU : U ≠ ⊤) :
    ∃ (p : ℕ) (U₁ : Subgroup C),
      p.Prime ∧ U ≤ U₁ ∧ U₁.index = p ∧
        (∀ q : C ⧸ U₁, q ^ p = 1) := by
  let Q := C ⧸ U
  letI : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hU
  letI : Finite (Subgroup Q) :=
    Finite.of_injective (fun H : Subgroup Q ↦ (H : Set Q)) SetLike.coe_injective
  obtain ⟨H, hH⟩ : ∃ H : Subgroup Q, IsCoatom H :=
    IsCoatomic.exists_coatom (Subgroup Q)
  letI : IsSimpleGroup (Q ⧸ H) :=
    simple_group_coatom H hH
  let p := Nat.card (Q ⧸ H)
  let qU := QuotientGroup.mk' U
  let U₁ : Subgroup C := H.comap qU
  have hp : p.Prime := IsSimpleGroup.prime_card
  have hqU : Function.Surjective qU := QuotientGroup.mk'_surjective U
  have hUU₁ : U ≤ U₁ := by
    intro x hx
    change qU x ∈ H
    rw [show qU x = 1 from (QuotientGroup.eq_one_iff _).2 hx]
    exact H.one_mem
  have hU₁index : U₁.index = p := by
    change (H.comap qU).index = Nat.card (Q ⧸ H)
    rw [H.index_comap_of_surjective hqU, H.index_eq_card]
  refine ⟨p, U₁, hp, hUU₁, hU₁index, ?_⟩
  intro x
  rw [← hU₁index]
  exact pow_card_eq_one'

/-- Pulling a subgroup back along a homomorphism whose range is `V` gives
the relative index inside `V`. -/
theorem comap_rel_range
    {D : Type*} [Group D] (f : D →* C)
    (U V : Subgroup C) (hUV : U ≤ V) (hrange : f.range = V) :
    (U.comap f).index = U.relIndex V := by
  subst V
  simpa only [Subgroup.relIndex] using U.index_comap f

/-- A preimage of a finite-index subgroup again has finite index. -/
theorem finiteIndex_comap
    {D : Type*} [Group D] (f : D →* C)
    (U : Subgroup C) [U.FiniteIndex] : (U.comap f).FiniteIndex := by
  constructor
  rw [U.index_comap f]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- In the prime-index step of Theorem VII.9.5, the norm-preimage has
index exactly the old index divided by the chosen prime. -/
theorem index_comap_div
    {D : Type*} [Group D] (f : D →* C)
    (U V : Subgroup C) (hUV : U ≤ V) (hrange : f.range = V)
    (p : ℕ) (hp : p.Prime) (hVindex : V.index = p) :
    (U.comap f).index = U.index / p := by
  rw [comap_rel_range f U V hUV hrange]
  apply Nat.eq_div_of_mul_eq_right hp.ne_zero
  simpa only [hVindex, Nat.mul_comm] using Subgroup.relIndex_mul_index hUV

/-- The prime-index pullback strictly decreases the index, which is the
well-founded measure in Milne's induction. -/
theorem index_comap_prime
    {D : Type*} [Group D] (f : D →* C)
    (U V : Subgroup C) [U.FiniteIndex]
    (hUV : U ≤ V) (hrange : f.range = V)
    (p : ℕ) (hp : p.Prime) (hVindex : V.index = p) :
    (U.comap f).index < U.index := by
  rw [index_comap_div f U V hUV hrange p hp hVindex]
  exact Nat.div_lt_self
    (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) hp.one_lt

end

end Towers.CField.NLimita
