import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Submission.NumberTheory.Splitting


/-!
# Milne, Chapter 8, Frobenius elements

The local Frobenius element acts on the finite residue extension by raising
to the cardinality of the base residue field.  Its order is the residue
degree.
-/

namespace Submission.NumberTheory.Milne

open Module
open scoped Pointwise

noncomputable section

variable (k l : Type*) [Field k] [Field l] [Fintype k] [Fintype l]
  [Algebra k l] [Algebra.IsAlgebraic k l]

omit [Fintype l] in
/-- The Frobenius element on a finite residue extension is the
`#k`-power map. -/
@[simp]
theorem field_frobenius_element (x : l) :
    FiniteField.frobeniusAlgEquivOfAlgebraic k l x =
      x ^ Fintype.card k :=
  rfl

omit [Fintype l] in
/-- The order of Frobenius is the residue degree. -/
theorem order_frobenius_element [Finite l] :
    orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic k l) = finrank k l := by
  letI := Fintype.ofFinite l
  exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k l

section Tower

variable (m : Type*) [Field m] [Fintype m]
  [Algebra k m] [Algebra l m] [IsScalarTower k l m]
  [Algebra.IsAlgebraic k m] [Algebra.IsAlgebraic l m]

omit [Algebra.IsAlgebraic k l] [Fintype m] [IsScalarTower k l m] in
/-- Milne 8.15 on residue fields: the Frobenius over the intermediate
residue field is the residue-degree power of the Frobenius over the base. -/
theorem frobenius_tower_pow (x : m) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic k m ^ finrank k l) x =
      FiniteField.frobeniusAlgEquivOfAlgebraic l m x := by
  rw [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  rw [← Module.card_eq_pow_finrank]

end Tower

section Naturality

variable {m : Type*} [Field m] [Fintype m] [Algebra k m]
  [Algebra.IsAlgebraic k m]

omit [Fintype l] [Fintype m] in
/-- Milne 8.16 and 8.17 on residue fields: Frobenius commutes with every
embedding over the base finite field.  Applying this to each field in a
tower, or to both factors of a compositum, gives the stated restriction
formulas. -/
theorem field_frobenius_naturality (e : l →ₐ[k] m) (x : l) :
    FiniteField.frobeniusAlgEquivOfAlgebraic k m (e x) =
      e (FiniteField.frobeniusAlgEquivOfAlgebraic k l x) := by
  rw [field_frobenius_element,
    field_frobenius_element, map_pow]

omit [Fintype l] [Fintype m] in
/-- Milne 8.14 on residue fields: conjugating Frobenius through an
equivalence of residue extensions gives Frobenius on the target. -/
theorem frobenius_conj_naturality (e : l ≃ₐ[k] m) (x : m) :
    e (FiniteField.frobeniusAlgEquivOfAlgebraic k l (e.symm x)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k m x := by
  simp

end Naturality

end

namespace IsArithFrobAt

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- Iterating an arithmetic Frobenius `n` times acts modulo the prime by
raising to the `n`th power of the residue-field cardinality. -/
theorem smul_sub_card
    {Q : Ideal S} [Q.IsPrime] {sigma : G}
    (hsigma : IsArithFrobAt R sigma Q) (n : ℕ) (x : S) :
    sigma ^ n • x - x ^ (Nat.card (R ⧸ Q.under R) ^ n) ∈ Q := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [← Ideal.Quotient.eq]
      have ih' := ih (sigma • x)
      rw [← Ideal.Quotient.eq] at ih'
      calc
        Ideal.Quotient.mk Q (sigma ^ (n + 1) • x) =
            Ideal.Quotient.mk Q (sigma ^ n • (sigma • x)) := by
          rw [pow_succ, mul_smul]
        _ = Ideal.Quotient.mk Q
            ((sigma • x) ^ (Nat.card (R ⧸ Q.under R) ^ n)) := ih'
        _ = (Ideal.Quotient.mk Q (sigma • x)) ^
            (Nat.card (R ⧸ Q.under R) ^ n) := by rw [map_pow]
        _ = ((Ideal.Quotient.mk Q x) ^
            Nat.card (R ⧸ Q.under R)) ^
              (Nat.card (R ⧸ Q.under R) ^ n) := by
          exact congrArg
            (fun y : S ⧸ Q => y ^ (Nat.card (R ⧸ Q.under R) ^ n))
            (hsigma.mk_apply x)
        _ = Ideal.Quotient.mk Q
            (x ^ (Nat.card (R ⧸ Q.under R) ^ (n + 1))) := by
          simp only [map_pow, pow_mul, Nat.pow_succ, Nat.mul_comm]

end IsArithFrobAt

section GlobalFrobenius

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/-- Milne 8.14, Frobenius-element part: at an unramified conjugate
prime, the Frobenius element is the conjugate of the original one. -/
theorem frobenius_conjugate_bot
    {P : Ideal S} {sigma sigma' : G}
    (hsigma : IsArithFrobAt R sigma P) (tau : G)
    (hsigma' : IsArithFrobAt R sigma' (tau • P))
    (hunram : (tau • P).inertia G = ⊥) :
    sigma' = tau * sigma * tau⁻¹ := by
  have hmem := hsigma'.mul_inv_mem_inertia (hsigma.conj tau)
  rw [hunram, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

/-- Milne's displayed formula 8.14 for Mathlib's chosen arithmetic
Frobenius elements. -/
theorem arith_frob_bot
    [Finite G] [Algebra.IsInvariant R S G]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)] (tau : G)
    [(tau • P).IsPrime] [Finite (S ⧸ (tau • P))]
    (hunram : (tau • P).inertia G = ⊥) :
    arithFrobAt R G (tau • P) = tau * arithFrobAt R G P * tau⁻¹ :=
  frobenius_conjugate_bot
    (IsArithFrobAt.arithFrobAt (R := R) (G := G) (Q := P)) tau
    (IsArithFrobAt.arithFrobAt (R := R) (G := G) (Q := tau • P)) hunram

end GlobalFrobenius

section UnramifiedFrobenius

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S]

/-- An arithmetic Frobenius preserves its prime, so it belongs to the
corresponding decomposition group. -/
theorem frobenius_mem_stabilizer
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)] :
    arithFrobAt R G P ∈ MulAction.stabilizer G P := by
  letI : FaithfulSMul G S := IsGaloisGroup.faithful R
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have h := Ideal.ext_iff.mp
    (IsArithFrobAt.arithFrobAt R G P).comap_eq
    ((arithFrobAt R G P)⁻¹ • x)
  change arithFrobAt R G P • ((arithFrobAt R G P)⁻¹ • x) ∈ P ↔
    (arithFrobAt R G P)⁻¹ • x ∈ P at h
  simpa only [smul_inv_smul] using h.symm

/-- At an unramified prime, the arithmetic Frobenius condition determines
the Galois element uniquely. -/
theorem arith_frob
    [IsDomain S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Algebra.IsUnramifiedAt R P] {sigma : G}
    (hsigma : IsArithFrobAt R sigma P) :
    sigma = arithFrobAt R G P := by
  letI : FaithfulSMul G S := IsGaloisGroup.faithful R
  apply MulSemiringAction.toAlgHom_injective R S
  exact hsigma.eq_of_isUnramifiedAt
    (IsArithFrobAt.arithFrobAt R G P)
      P.primeCompl_le_nonZeroDivisors

/-- Milne 8.14: for an unramified prime, Frobenius at a conjugate prime is
the conjugate of Frobenius at the original prime. -/
theorem arith_frob_conjugate
    [IsDomain S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    (tau : G) [Finite (S ⧸ tau • P)]
    [Algebra.IsUnramifiedAt R P] :
    arithFrobAt R G (tau • P) = tau * arithFrobAt R G P * tau⁻¹ := by
  letI : FaithfulSMul G S := IsGaloisGroup.faithful R
  have hconj : IsArithFrobAt R
      (tau⁻¹ * arithFrobAt R G (tau • P) * tau) P := by
    simpa only [inv_inv, inv_smul_smul] using
      (IsArithFrobAt.arithFrobAt R G (tau • P)).conj tau⁻¹
  have h : tau⁻¹ * arithFrobAt R G (tau • P) * tau =
      arithFrobAt R G P := by
    apply MulSemiringAction.toAlgHom_injective R S
    exact hconj.eq_of_isUnramifiedAt
      (IsArithFrobAt.arithFrobAt R G P)
      P.primeCompl_le_nonZeroDivisors
  rw [← h]
  group

/-- At an unramified prime, the inertia subgroup is trivial.  This is the
group-theoretic form of uniqueness of arithmetic Frobenius. -/
theorem inertia_bot_unramified
    [IsDomain S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Algebra.IsUnramifiedAt R P] :
    P.inertia G = ⊥ := by
  apply le_antisymm
  · intro tau htau
    rw [Subgroup.mem_bot]
    let sigma := arithFrobAt R G P
    have hsigma : IsArithFrobAt R sigma P :=
      IsArithFrobAt.arithFrobAt R G P
    have htau_mem {x : S} (hx : x ∈ P) : tau • x ∈ P := by
      simpa only [sub_add_cancel] using P.add_mem (htau x) hx
    have hmul : IsArithFrobAt R (tau * sigma) P := by
      intro x
      have h₁ : tau •
          (sigma • x - x ^ Nat.card (R ⧸ P.under R)) ∈ P :=
        htau_mem (hsigma x)
      have h₂ : tau • (x ^ Nat.card (R ⧸ P.under R)) -
          x ^ Nat.card (R ⧸ P.under R) ∈ P :=
        htau (x ^ Nat.card (R ⧸ P.under R))
      change (tau * sigma) • x - x ^ Nat.card (R ⧸ P.under R) ∈ P
      simpa only [smul_sub, mul_smul, sub_add_sub_cancel] using P.add_mem h₁ h₂
    have h := arith_frob P hmul
    apply mul_right_cancel (b := sigma)
    simpa only [one_mul] using h
  · exact bot_le

set_option maxHeartbeats 1000000 in
-- Residue-field and stabilizer quotient instances require deeper synthesis.
attribute [local instance] Ideal.Quotient.field in
/-- At an unramified prime, the order of arithmetic Frobenius is the residue
degree.  This is the order statement underlying the local-degree calculation
in Lemma VIII.4.1. -/
theorem frob_inertia_deg
    [IsDomain S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] [P.IsMaximal] [Finite (S ⧸ P)]
    [Finite (R ⧸ P.under R)] [(P.under R).IsMaximal]
    [Algebra.IsUnramifiedAt R P] :
    orderOf (arithFrobAt R G P) =
      (P.under R).inertiaDeg P := by
  let p := P.under R
  letI : P.LiesOver p := ⟨rfl⟩
  letI : Fintype (R ⧸ p) := Fintype.ofFinite _
  letI : Fintype (S ⧸ P) := Fintype.ofFinite _
  let sigma : MulAction.stabilizer G P :=
    ⟨arithFrobAt R G P, frobenius_mem_stabilizer P⟩
  let residueRestriction := Ideal.Quotient.stabilizerHom P p G
  have hrestriction_injective : Function.Injective residueRestriction := by
    apply (MonoidHom.ker_eq_bot_iff residueRestriction).mp
    rw [Ideal.Quotient.ker_stabilizerHom,
      inertia_bot_unramified (R := R) (G := G) P]
    ext tau
    simp
  have hrestriction : residueRestriction sigma =
      FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ P) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk P (arithFrobAt R G P • x) = _
    simpa only [field_frobenius_element,
      Nat.card_eq_fintype_card] using
        (IsArithFrobAt.arithFrobAt R G P).mk_apply x
  calc
    orderOf (arithFrobAt R G P) = orderOf sigma :=
      orderOf_submonoid sigma
    _ = orderOf (residueRestriction sigma) :=
      (orderOf_injective residueRestriction hrestriction_injective sigma).symm
    _ = orderOf
        (FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ p) (S ⧸ P)) := by
      rw [hrestriction]
    _ = Module.finrank (R ⧸ p) (S ⧸ P) :=
      order_frobenius_element (R ⧸ p) (S ⧸ P)
    _ = p.inertiaDeg P := (Ideal.inertiaDeg_algebraMap p P).symm

attribute [local instance] Ideal.Quotient.field in
/-- Milne 8.15: in a tower, the Frobenius over the intermediate field is
the residue-degree power of the Frobenius over the base field.  The map
`embed` identifies the smaller Galois group with its action inside the
larger one. -/
theorem arith_frob_tower
    {T H : Type*} [CommRing T] [Algebra R T] [Algebra T S]
    [IsScalarTower R T S]
    [Group H] [Finite H] [MulSemiringAction H S] [IsGaloisGroup H T S]
    [IsDomain S] [IsNoetherianRing S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [(P.under R).IsMaximal] [(P.under T).IsMaximal]
    [(P.under T).LiesOver (P.under R)]
    [Finite (R ⧸ P.under R)] [Finite (T ⧸ P.under T)]
    [Algebra.IsUnramifiedAt R P]
    (embed : H →* G)
    (embed_smul : ∀ tau : H, ∀ x : S, embed tau • x = tau • x) :
    arithFrobAt R G P ^ (P.under R).inertiaDeg (P.under T) =
      embed (arithFrobAt T H P) := by
  let f := (P.under R).inertiaDeg (P.under T)
  let sigma := arithFrobAt R G P
  let tau := arithFrobAt T H P
  have hcard : Nat.card (T ⧸ P.under T) =
      Nat.card (R ⧸ P.under R) ^ f := by
    dsimp only [f]
    rw [Ideal.inertiaDeg_algebraMap]
    exact Module.natCard_eq_pow_finrank
      (K := R ⧸ P.under R) (V := T ⧸ P.under T)
  have hsigma : IsArithFrobAt R sigma P :=
    IsArithFrobAt.arithFrobAt R G P
  have htau : IsArithFrobAt T tau P :=
    IsArithFrobAt.arithFrobAt T H P
  have hmem : sigma ^ f * (embed tau)⁻¹ ∈ P.inertia G := by
    intro x
    let y := (embed tau)⁻¹ • x
    have hpow := IsArithFrobAt.smul_sub_card
      (R := R) hsigma f y
    have htau' := htau y
    rw [hcard] at htau'
    have hembed : embed tau • y -
        y ^ (Nat.card (R ⧸ P.under R) ^ f) ∈ P := by
      simpa only [embed_smul] using htau'
    have hsub : sigma ^ f • y - embed tau • y ∈ P := by
      convert P.sub_mem hpow hembed using 1 ; ring
    simpa only [y, mul_smul, smul_inv_smul] using hsub
  rw [inertia_bot_unramified (R := R) (G := G) P,
    Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

/-- Milne 8.16: restricting Frobenius to a Galois intermediate extension
gives the Frobenius at the contracted prime. -/
theorem arith_restrict
    {T H : Type*} [CommRing T] [Algebra R T] [Algebra T S]
    [IsScalarTower R T S]
    [Group H] [Finite H] [MulSemiringAction H T] [IsGaloisGroup H R T]
    [IsDomain T] [IsNoetherianRing T]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Finite (T ⧸ P.under T)] [Algebra.IsUnramifiedAt R (P.under T)]
    (res : G →* H)
    (res_smul : ∀ sigma : G, ∀ x : T,
      algebraMap T S (res sigma • x) = sigma • algebraMap T S x) :
    res (arithFrobAt R G P) = arithFrobAt R H (P.under T) := by
  have hres : IsArithFrobAt R (res (arithFrobAt R G P)) (P.under T) := by
    intro x
    rw [Ideal.mem_of_liesOver
      (A := T) (B := S) (p := P.under T) (P := P)]
    have h := (IsArithFrobAt.arithFrobAt R G P) (algebraMap T S x)
    change algebraMap T S
      (res (arithFrobAt R G P) • x -
        x ^ Nat.card (R ⧸ (P.under T).under R)) ∈ P
    rw [map_sub, map_pow, res_smul, Ideal.under_under]
    exact h
  exact arith_frob (R := R) (S := T) (G := H)
    (P.under T) hres

/-- Milne 8.16 with the book's hypothesis that the prime upstairs is
unramified over the base.  Unramifiedness descends to the contracted prime. -/
theorem arith_restrict_unramified
    {T H : Type*} [CommRing T] [Algebra R T] [Algebra T S]
    [IsScalarTower R T S]
    [Group H] [Finite H] [MulSemiringAction H T] [IsGaloisGroup H R T]
    [IsDomain T] [IsNoetherianRing T]
    [Algebra.EssFiniteType R T] [Algebra.EssFiniteType R S]
    [IsDedekindDomain T] [Module.IsTorsionFree T S]
    [IsDomain S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Finite (T ⧸ P.under T)] [Algebra.IsUnramifiedAt R P]
    (res : G →* H)
    (res_smul : ∀ sigma : G, ∀ x : T,
      algebraMap T S (res sigma • x) = sigma • algebraMap T S x) :
    res (arithFrobAt R G P) = arithFrobAt R H (P.under T) := by
  letI : Algebra.IsUnramifiedAt R (P.under T) :=
    Algebra.IsUnramifiedAt.of_liesOver R (P.under T) P
  exact arith_restrict (R := R) (S := S) (G := G) P res res_smul

/-- Milne 8.17: under the product of the two restriction maps from a
compositum, Frobenius maps to the pair of Frobenius elements. -/
theorem arith_frob_unramified
    {T₁ T₂ H₁ H₂ : Type*}
    [CommRing T₁] [CommRing T₂]
    [Algebra R T₁] [Algebra T₁ S] [IsScalarTower R T₁ S]
    [Algebra R T₂] [Algebra T₂ S] [IsScalarTower R T₂ S]
    [Group H₁] [Finite H₁] [MulSemiringAction H₁ T₁] [IsGaloisGroup H₁ R T₁]
    [Group H₂] [Finite H₂] [MulSemiringAction H₂ T₂] [IsGaloisGroup H₂ R T₂]
    [IsDomain T₁] [IsDomain T₂]
    [IsNoetherianRing T₁] [IsNoetherianRing T₂]
    [Algebra.EssFiniteType R T₁] [Algebra.EssFiniteType R T₂]
    [Algebra.EssFiniteType R S]
    [IsDedekindDomain T₁] [IsDedekindDomain T₂]
    [Module.IsTorsionFree T₁ S] [Module.IsTorsionFree T₂ S]
    [IsDomain S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Finite (T₁ ⧸ P.under T₁)] [Finite (T₂ ⧸ P.under T₂)]
    [Algebra.IsUnramifiedAt R P]
    (res₁ : G →* H₁) (res₂ : G →* H₂)
    (res₁_smul : ∀ sigma : G, ∀ x : T₁,
      algebraMap T₁ S (res₁ sigma • x) = sigma • algebraMap T₁ S x)
    (res₂_smul : ∀ sigma : G, ∀ x : T₂,
      algebraMap T₂ S (res₂ sigma • x) = sigma • algebraMap T₂ S x) :
    (res₁.prod res₂) (arithFrobAt R G P) =
      (arithFrobAt R H₁ (P.under T₁), arithFrobAt R H₂ (P.under T₂)) := by
  apply Prod.ext
  · exact arith_restrict_unramified
      (R := R) (S := S) (G := G) P res₁ res₁_smul
  · exact arith_restrict_unramified
      (R := R) (S := S) (G := G) P res₂ res₂_smul

/-- Milne, after 8.17: when the product of the two restriction maps is
injective (as it is for a compositum), the Frobenius upstairs is trivial
exactly when both restricted Frobenius elements are trivial.  Combined with
the Frobenius criterion for complete splitting, this says that an unramified
prime splits completely in the compositum exactly when it splits completely
in both factors. -/
theorem arith_frob_restrictions
    {T₁ T₂ H₁ H₂ : Type*}
    [CommRing T₁] [CommRing T₂]
    [Algebra R T₁] [Algebra T₁ S] [IsScalarTower R T₁ S]
    [Algebra R T₂] [Algebra T₂ S] [IsScalarTower R T₂ S]
    [Group H₁] [Finite H₁] [MulSemiringAction H₁ T₁] [IsGaloisGroup H₁ R T₁]
    [Group H₂] [Finite H₂] [MulSemiringAction H₂ T₂] [IsGaloisGroup H₂ R T₂]
    [IsDomain T₁] [IsDomain T₂]
    [IsNoetherianRing T₁] [IsNoetherianRing T₂]
    [Algebra.EssFiniteType R T₁] [Algebra.EssFiniteType R T₂]
    [Algebra.EssFiniteType R S]
    [IsDedekindDomain T₁] [IsDedekindDomain T₂]
    [Module.IsTorsionFree T₁ S] [Module.IsTorsionFree T₂ S]
    [IsDomain S]
    (P : Ideal S) [P.IsPrime] [Finite (S ⧸ P)]
    [Finite (T₁ ⧸ P.under T₁)] [Finite (T₂ ⧸ P.under T₂)]
    [Algebra.IsUnramifiedAt R P]
    (res₁ : G →* H₁) (res₂ : G →* H₂)
    (res₁_smul : ∀ sigma : G, ∀ x : T₁,
      algebraMap T₁ S (res₁ sigma • x) = sigma • algebraMap T₁ S x)
    (res₂_smul : ∀ sigma : G, ∀ x : T₂,
      algebraMap T₂ S (res₂ sigma • x) = sigma • algebraMap T₂ S x)
    (hinjective : Function.Injective (res₁.prod res₂)) :
    arithFrobAt R G P = 1 ↔
      arithFrobAt R H₁ (P.under T₁) = 1 ∧
        arithFrobAt R H₂ (P.under T₂) = 1 := by
  have hrestrict := arith_frob_unramified
    (R := R) (S := S) (G := G) P res₁ res₂ res₁_smul res₂_smul
  constructor
  · intro htop
    rw [htop, map_one] at hrestrict
    exact Prod.mk_eq_one.mp hrestrict.symm
  · rintro ⟨h₁, h₂⟩
    apply hinjective
    rw [map_one, hrestrict, h₁, h₂]
    rfl

end UnramifiedFrobenius

section NumberFieldFrobeniusIdentity

open NumberField
open scoped NumberField

variable {K L : Type*} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

noncomputable local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)

local instance : IsGaloisGroup Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  IsGaloisGroup.of_isFractionRing Gal(L/K)
    (RingOfIntegers K) (RingOfIntegers L) K L

/-- At an unramified finite prime of a Galois extension of number fields,
the arithmetic Frobenius is the identity exactly when the residue degree is
one. -/
theorem number_frob_deg
    (P : Ideal (RingOfIntegers L)) [P.IsPrime]
    [Finite (RingOfIntegers L ⧸ P)]
    [Algebra.IsUnramifiedAt (RingOfIntegers K) P] :
    arithFrobAt (RingOfIntegers K) Gal(L/K) P = 1 ↔
      Ideal.inertiaDeg (P.under (RingOfIntegers K)) P = 1 := by
  let p : Ideal (RingOfIntegers K) := P.under (RingOfIntegers K)
  letI : P.LiesOver p := ⟨rfl⟩
  have hP0 : P ≠ ⊥ := by
    intro hP
    subst P
    letI : Finite (RingOfIntegers L) :=
      Finite.of_equiv (RingOfIntegers L ⧸ (⊥ : Ideal (RingOfIntegers L)))
        (RingEquiv.quotientBot (RingOfIntegers L))
    exact RingOfIntegers.not_isField L
      (Finite.isField_of_domain (RingOfIntegers L))
  have hp0 : p ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
  have hpprime : p.IsPrime := inferInstance
  letI : p.IsMaximal := hpprime.isMaximal hp0
  letI : Field (RingOfIntegers K ⧸ p) := Ideal.Quotient.field p
  haveI : Finite (RingOfIntegers K ⧸ p) :=
    Ideal.finiteQuotientOfFreeOfNeBot p hp0
  letI : Fintype (RingOfIntegers K ⧸ p) := Fintype.ofFinite _
  letI : P.IsMaximal := Ideal.IsPrime.isMaximal
    (show P.IsPrime from inferInstance) hP0
  letI : Field (RingOfIntegers L ⧸ P) := Ideal.Quotient.field P
  let sigma : Gal(L/K) := arithFrobAt (RingOfIntegers K) Gal(L/K) P
  have hsigma : IsArithFrobAt (RingOfIntegers K) sigma P :=
    IsArithFrobAt.arithFrobAt (RingOfIntegers K) Gal(L/K) P
  constructor
  · intro hsigma1
    have hrestrict_id : hsigma.restrict = 1 := by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [AlgHom.IsArithFrobAt.restrict_mk, sigma, hsigma1]
    have hrestrict_frob :
        hsigma.restrict =
          FiniteField.frobeniusAlgHom
            (RingOfIntegers K ⧸ p) (RingOfIntegers L ⧸ P) := by
      ext x
      simp [p, AlgHom.IsArithFrobAt.restrict_apply, Nat.card_eq_fintype_card]
    have hfinrank :
        Module.finrank (RingOfIntegers K ⧸ p) (RingOfIntegers L ⧸ P) = 1 := by
      have horder :
          orderOf (FiniteField.frobeniusAlgHom
            (RingOfIntegers K ⧸ p) (RingOfIntegers L ⧸ P)) = 1 := by
        rw [← hrestrict_frob, hrestrict_id]
        exact orderOf_one
      rw [FiniteField.orderOf_frobeniusAlgHom] at horder
      exact horder
    simpa [p] using
      (Ideal.inertiaDeg_algebraMap (p := p) (P := P)).trans hfinrank
  · intro hf
    have hfinrank :
        Module.finrank (RingOfIntegers K ⧸ p) (RingOfIntegers L ⧸ P) = 1 := by
      simpa [p] using hf
    have hfrob_id :
        FiniteField.frobeniusAlgHom
          (RingOfIntegers K ⧸ p) (RingOfIntegers L ⧸ P) = 1 := by
      apply (orderOf_eq_one_iff).mp
      rw [FiniteField.orderOf_frobeniusAlgHom, hfinrank]
    have hrestrict_frob :
        hsigma.restrict =
          FiniteField.frobeniusAlgHom
            (RingOfIntegers K ⧸ p) (RingOfIntegers L ⧸ P) := by
      ext x
      simp [p, AlgHom.IsArithFrobAt.restrict_apply, Nat.card_eq_fintype_card]
    have hrestrict_id : hsigma.restrict = 1 := by
      rw [hrestrict_frob, hfrob_id]
    have hone : IsArithFrobAt (RingOfIntegers K) (1 : Gal(L/K)) P := by
      intro x
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      change
        Ideal.Quotient.mk P ((1 : Gal(L/K)) • x) -
            (Ideal.Quotient.mk P x) ^
              Nat.card (RingOfIntegers K ⧸ Ideal.under (RingOfIntegers K) P) = 0
      apply sub_eq_zero.mpr
      calc
        Ideal.Quotient.mk P ((1 : Gal(L/K)) • x) = Ideal.Quotient.mk P x := by
          simp
        _ = hsigma.restrict (Ideal.Quotient.mk P x) := by
          simp [hrestrict_id]
        _ = (Ideal.Quotient.mk P x) ^
              Nat.card (RingOfIntegers K ⧸ Ideal.under (RingOfIntegers K) P) :=
          hsigma.restrict_apply (Ideal.Quotient.mk P x)
    exact (arith_frob P hone).symm

end NumberFieldFrobeniusIdentity

section CompleteSplitting

open NumberField

/-- Milne, after formula 8.17: an unramified rational prime splits
completely in a finite Galois number field exactly when its arithmetic
Frobenius element is the identity.  The statement is independent of the
chosen prime above the rational prime by the conjugacy formula 8.14. -/
theorem splits_completely_arith
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    {q : ℕ} (hq : Nat.Prime q)
    (Q : Ideal (RingOfIntegers K)) [Q.IsPrime]
    [Q.LiesOver (Ideal.rationalPrimeIdeal q)]
    [Finite (RingOfIntegers K ⧸ Q)]
    [Algebra.IsUnramifiedAt ℤ Q] :
    Submission.splitsCompletely K q ↔
      arithFrobAt ℤ Gal(K/ℚ) Q = 1 := by
  exact completely_arith_frob
    K hq Q (arithFrobAt ℤ Gal(K/ℚ) Q)
      (IsArithFrobAt.arithFrobAt ℤ Gal(K/ℚ) Q)

end CompleteSplitting

end Submission.NumberTheory.Milne
