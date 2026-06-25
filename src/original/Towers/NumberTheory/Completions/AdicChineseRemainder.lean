import Towers.NumberTheory.Completions.AdicBaseChange
import Towers.NumberTheory.Completions.AdicCompletionPower
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Chinese remaindering adic completions

This file lifts the Chinese remainder theorem for powers of a finite family
of pairwise coprime ideals toward an equivalence of their adic completions.
It is the decomposition step for a completed semilocal Dedekind lattice.
-/

namespace Towers.NumberTheory.Milne

open Function
open scoped BigOperators

noncomputable section

universe u

variable {R ι : Type u} [CommRing R] [Fintype ι]

private theorem prod_i_inf
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P)) (n : ℕ) :
    (∏ i, P i) ^ n = ⨅ i, P i ^ n := by
  calc
    (∏ i, P i) ^ n = ∏ i, P i ^ n := by rw [Finset.prod_pow]
    _ = ⨅ i ∈ Finset.univ, P i ^ n :=
      Ideal.prod_eq_iInf_of_pairwise_isCoprime (by
        intro i _ j _ hij
        exact (hP hij).pow)
    _ = ⨅ i, P i ^ n := by simp

/-- At every level, the quotient by a power of a product of pairwise
coprime ideals is the product of the corresponding power quotients.  The
statement uses the exact quotient submodules appearing in `AdicCompletion`.
-/
def adicChineseRemainder
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P)) (n : ℕ) :
    (R ⧸ ((∏ i, P i) ^ n • (⊤ : Submodule R R))) ≃+*
      (∀ i, R ⧸ (P i ^ n • (⊤ : Submodule R R))) :=
  (Ideal.quotEquivOfEq (by simp)).trans <|
    (Ideal.quotEquivOfEq (prod_i_inf P hP n)).trans <|
      (Ideal.quotientInfRingEquivPiQuotient (fun i => P i ^ n)
        (fun i j hij => (hP hij).pow)).trans <|
          RingEquiv.piCongrRight fun i => Ideal.quotEquivOfEq (by simp)

@[simp]
theorem chinese_remainder_mk
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P))
    (n : ℕ) (x : R) :
    adicChineseRemainder P hP n
        (Submodule.mkQ ((∏ i, P i) ^ n • (⊤ : Submodule R R)) x) =
      fun i => Submodule.mkQ (P i ^ n • (⊤ : Submodule R R)) x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The transition comparison unfolds the quotient equivalence in every coordinate.
/-- The quotient Chinese remainder equivalences commute with the transition
maps of the adic inverse systems. -/
theorem adic_chinese_remainder
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P))
    {m n : ℕ} (hmn : m ≤ n)
    (x : R ⧸ ((∏ i, P i) ^ n • (⊤ : Submodule R R))) :
    (fun i => AdicCompletion.transitionMap (P i) R hmn
        (adicChineseRemainder P hP n x i)) =
      adicChineseRemainder P hP m
        (AdicCompletion.transitionMap (∏ i, P i) R hmn x) := by
  funext i
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      change AdicCompletion.transitionMap (P i) R hmn
          (adicChineseRemainder P hP n
            (Submodule.mkQ ((∏ i, P i) ^ n • (⊤ : Submodule R R)) x) i) =
        adicChineseRemainder P hP m
          (AdicCompletion.transitionMap (∏ i, P i) R hmn
            (Submodule.mkQ ((∏ i, P i) ^ n • (⊤ : Submodule R R)) x)) i
      rw [chinese_remainder_mk]
      change Submodule.factor _ (Submodule.mkQ _ x) =
        adicChineseRemainder P hP m
          (Submodule.factor _ (Submodule.mkQ _ x)) i
      rw [Submodule.factor_mk, Submodule.factor_mk]
      rw [chinese_remainder_mk]

/-- The inverse quotient Chinese remainder equivalences commute with the
transition maps. -/
theorem chinese_remainder_transition
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P))
    {m n : ℕ} (hmn : m ≤ n)
    (x : ∀ i, R ⧸ (P i ^ n • (⊤ : Submodule R R))) :
    AdicCompletion.transitionMap (∏ i, P i) R hmn
        ((adicChineseRemainder P hP n).symm x) =
      (adicChineseRemainder P hP m).symm
        (fun i => AdicCompletion.transitionMap (P i) R hmn (x i)) := by
  apply (adicChineseRemainder P hP m).injective
  rw [RingEquiv.apply_symm_apply]
  rw [← adic_chinese_remainder]
  rw [RingEquiv.apply_symm_apply]

/-- The canonical map from completion at a product of pairwise coprime
ideals to the product of their completions. -/
def chineseRemainderHom
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P)) :
    AdicCompletion (∏ i, P i) R →+*
      (∀ i, AdicCompletion (P i) R) where
  toFun x i := ⟨fun n =>
      adicChineseRemainder P hP n (x.val n) i,
    fun hmn => by
      simpa only [x.property hmn] using congrFun
        (adic_chinese_remainder
          P hP hmn (x.val _)) i⟩
  map_zero' := by
    funext i
    apply AdicCompletion.ext
    intro n
    exact congrFun
      (map_zero (adicChineseRemainder P hP n)) i
  map_add' x y := by
    funext i
    apply AdicCompletion.ext
    intro n
    exact congrFun
      (map_add (adicChineseRemainder P hP n)
        (x.val n) (y.val n)) i
  map_one' := by
    funext i
    apply AdicCompletion.ext
    intro n
    exact congrFun
      (map_one (adicChineseRemainder P hP n)) i
  map_mul' x y := by
    funext i
    apply AdicCompletion.ext
    intro n
    exact congrFun
      (map_mul (adicChineseRemainder P hP n)
        (x.val n) (y.val n)) i

/-- The coordinatewise inverse to the completed Chinese remainder map. -/
def chineseRemainderInv
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P))
    (x : ∀ i, AdicCompletion (P i) R) :
    AdicCompletion (∏ i, P i) R :=
  ⟨fun n => (adicChineseRemainder P hP n).symm
      (fun i => (x i).val n),
    fun hmn => by
      rw [chinese_remainder_transition]
      congr 2
      funext i
      exact (x i).property hmn⟩

/-- Completion at a finite product of pairwise coprime ideals is the product
of the completions at the individual ideals. -/
def chineseRemainderRing
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P)) :
    AdicCompletion (∏ i, P i) R ≃+*
      (∀ i, AdicCompletion (P i) R) where
  __ := chineseRemainderHom P hP
  invFun := chineseRemainderInv P hP
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (adicChineseRemainder P hP n).symm_apply_apply
      (x.val n)
  right_inv x := by
    funext i
    apply AdicCompletion.ext
    intro n
    exact congrFun
      ((adicChineseRemainder P hP n).apply_symm_apply
        (fun i => (x i).val n)) i

@[simp]
theorem chinese_remainder_ring
    (P : ι → Ideal R) (hP : Pairwise (IsCoprime on P)) (x : R) :
    chineseRemainderRing P hP
        (AdicCompletion.of (∏ i, P i) R x) =
      fun i => AdicCompletion.of (P i) R x := by
  funext i
  apply AdicCompletion.ext
  intro n
  rfl

section Dedekind

variable [IsDomain R] [IsDedekindDomain R]

open Ideal UniqueFactorizationMonoid

open scoped Classical in
/-- The completion of a Dedekind domain at a nonzero ideal is the product of
the completions at the powers of its distinct prime factors. -/
def adicCompletionPi (I : Ideal R) (hI : I ≠ ⊥) :
    AdicCompletion I R ≃+*
      (∀ P : (factors I).toFinset,
        AdicCompletion
          ((P : Ideal R) ^ Multiset.count (P : Ideal R) (factors I)) R) := by
  let F := (factors I).toFinset
  let Q : F → Ideal R := fun P =>
    (P : Ideal R) ^ Multiset.count (P : Ideal R) (factors I)
  have hprime (P : F) : Prime (P : Ideal R) :=
    prime_of_factor (P : Ideal R) (Multiset.mem_toFinset.mp P.prop)
  have hcoprime : Pairwise (IsCoprime on Q) := by
    intro P P' hPP'
    apply IsCoprime.pow
    exact Ideal.isCoprime_iff_sup_eq.mpr <|
      IsMaximal.coprime_of_ne
        (IsPrime.isMaximal (Ideal.isPrime_of_prime (hprime P)) (hprime P).ne_zero)
        (IsPrime.isMaximal (Ideal.isPrime_of_prime (hprime P')) (hprime P').ne_zero)
        (Subtype.coe_injective.ne hPP')
  have hprod : ∏ P : F, Q P = I := by
    calc
      (∏ P : F, Q P) =
          ∏ P ∈ (factors I).toFinset,
            P ^ Multiset.count P (factors I) := by
        exact (factors I).toFinset.prod_coe_sort
          (fun P => P ^ Multiset.count P (factors I))
      _ = ((factors I).map fun P => P).prod :=
        (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).prod := by rw [Multiset.map_id']
      _ = I := associated_iff_eq.mp (factors_prod hI)
  let e := chineseRemainderRing Q hcoprime
  exact (RingEquiv.cast
    (R := fun J : Ideal R => AdicCompletion J R) hprod).symm.trans e

open scoped Classical in
/-- The completion of a Dedekind domain at a nonzero ideal is the product of
the completions at its distinct prime factors. -/
def adicPiFactors (I : Ideal R) (hI : I ≠ ⊥) :
    AdicCompletion I R ≃+*
      (∀ P : (factors I).toFinset, AdicCompletion (P : Ideal R) R) :=
  (adicCompletionPi I hI).trans <|
    RingEquiv.piCongrRight fun P =>
      adicPowRing (P : Ideal R)
        (Multiset.count (P : Ideal R) (factors I))
        (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.prop))

end Dedekind

end

end Towers.NumberTheory.Milne
