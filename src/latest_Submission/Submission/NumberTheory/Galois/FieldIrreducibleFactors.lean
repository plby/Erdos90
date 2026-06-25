import Mathlib.FieldTheory.Finite.Extension


/-!
# Milne, Chapter 8, Remark 8.29: factors of `X^(q^n) - X`

The irreducible factors of `X^(q^n) - X` over the finite field of cardinality
`q` have degrees dividing `n`.  This is the theoretical statement behind
Milne's suggestion to find irreducible polynomials by factoring this
polynomial.  The explicit PARI computations in the remark are not formalized.
-/

namespace Submission.NumberTheory.Milne

open Polynomial
open scoped Polynomial

variable {k : Type*} [Field k] [Finite k]

/-- Milne, Remark 8.29: every monic irreducible polynomial of degree `n`
over a finite field of cardinality `q` divides `X ^ (q ^ n) - X`. -/
theorem irreducible_dvd_x
    {f : k[X]} (hf : Irreducible f) (hmonic : f.Monic) :
    f ∣ X ^ (Nat.card k) ^ f.natDegree - X := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  letI : Module.Finite k (AdjoinRoot f) := hmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot f) := Module.finite_of_finite k
  letI : Fintype (AdjoinRoot f) := Fintype.ofFinite (AdjoinRoot f)
  have hcard : Nat.card (AdjoinRoot f) =
      Nat.card k ^ f.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := k) (V := AdjoinRoot f),
      (AdjoinRoot.powerBasis hf.ne_zero).finrank]
    rfl
  have hpow : AdjoinRoot.root f ^ Nat.card (AdjoinRoot f) =
      AdjoinRoot.root f := by
    simpa only [Fintype.card_eq_nat_card] using
      FiniteField.pow_card (AdjoinRoot.root f)
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  simp only [map_sub, map_pow, aeval_X]
  change AdjoinRoot.root f ^ (Nat.card k) ^ f.natDegree -
    AdjoinRoot.root f = 0
  rw [← hcard, hpow, sub_self]

omit [Finite k] in
/-- Milne, Remark 8.29: an irreducible factor of `X^(q^n) - X` over the
finite field of cardinality `q` has degree dividing `n`. -/
theorem irreducible_x_sub
    {n : ℕ} {f : k[X]} (hf : Irreducible f)
    (hdiv : f ∣ X ^ (Nat.card k) ^ n - X) :
    f.natDegree ∣ n :=
  hf.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdiv

omit [Finite k] in
/-- In Milne's example with `q = 5` and `n = 3`, every irreducible factor
has degree one or three.  The conclusion in fact holds over every finite
field when the exponent is `q^3`. -/
theorem irreducible_x_cube
    {f : k[X]} (hf : Irreducible f)
    (hdiv : f ∣ X ^ (Nat.card k) ^ 3 - X) :
    f.natDegree = 1 ∨ f.natDegree = 3 := by
  exact (Nat.dvd_prime Nat.prime_three).mp
    (irreducible_x_sub hf hdiv)

private local instance primeFiveFact : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem dvd_x_125
    {ι : Type*} [Fintype ι] (g : ι → (ZMod 5)[X])
    (hfactor : X ^ (Nat.card (ZMod 5)) ^ 3 - X = ∏ i, g i) (i : ι) :
    g i ∣ X ^ (Nat.card (ZMod 5)) ^ 3 - X := by
  rw [hfactor]
  exact Finset.dvd_prod_of_mem g (Finset.mem_univ i)

private theorem factor_or_three
    {ι : Type*} [Fintype ι] (g : ι → (ZMod 5)[X])
    (hfactor : X ^ (Nat.card (ZMod 5)) ^ 3 - X = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i)) (i : ι) :
    (g i).natDegree = 1 ∨ (g i).natDegree = 3 :=
  irreducible_x_cube
    (hirr i) (dvd_x_125 g hfactor i)

private def linearFactorRoot
    {ι : Type*} (g : ι → (ZMod 5)[X])
    (i : {i : ι // (g i).natDegree = 1}) : ZMod 5 :=
  -(g i).coeff 0

private theorem linear_x_c
    {ι : Type*} (g : ι → (ZMod 5)[X])
    (hmonic : ∀ i, (g i).Monic)
    (i : {i : ι // (g i).natDegree = 1}) :
    g i = X - C (linearFactorRoot g i) := by
  rw [(hmonic i).eq_X_add_C i.property]
  simp [linearFactorRoot, sub_eq_add_neg]

private theorem linear_root_injective
    {ι : Type*} (g : ι → (ZMod 5)[X])
    (hmonic : ∀ i, (g i).Monic) (hinj : Function.Injective g) :
    Function.Injective (linearFactorRoot g) := by
  intro i j hij
  apply Subtype.ext
  apply hinj
  rw [linear_x_c g hmonic i,
    linear_x_c g hmonic j, hij]

set_option maxRecDepth 4000 in
private theorem linear_root_surjective
    {ι : Type*} [Fintype ι] (g : ι → (ZMod 5)[X])
    (hfactor : X ^ (Nat.card (ZMod 5)) ^ 3 - X = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i)) (hmonic : ∀ i, (g i).Monic) :
    Function.Surjective (linearFactorRoot g) := by
  classical
  intro a
  have ha : a ^ (Nat.card (ZMod 5)) ^ 3 = a :=
    by simpa only [Fintype.card_eq_nat_card] using FiniteField.pow_card_pow 3 a
  have hdiv : X - C a ∣ X ^ (Nat.card (ZMod 5)) ^ 3 - X := by
    rw [dvd_iff_isRoot, IsRoot]
    simp only [eval_sub, eval_pow, eval_X, ha, sub_self]
  rw [hfactor] at hdiv
  obtain ⟨i, -, hi⟩ :=
    (Prime.dvd_finsetProd_iff (irreducible_X_sub_C a).prime g).mp hdiv
  have hassoc : Associated (X - C a) (g i) :=
    (irreducible_X_sub_C a).associated_of_dvd (hirr i) hi
  have heq : X - C a = g i :=
    eq_of_monic_of_associated (monic_X_sub_C a) (hmonic i) hassoc
  have hidegree : (g i).natDegree = 1 := by
    rw [← heq]
    exact natDegree_X_sub_C a
  refine ⟨⟨i, hidegree⟩, ?_⟩
  simp only [linearFactorRoot]
  rw [← heq]
  simp

private theorem card_x_125
    {ι : Type*} [Fintype ι] (g : ι → (ZMod 5)[X])
    (hfactor : X ^ (Nat.card (ZMod 5)) ^ 3 - X = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i)) (hmonic : ∀ i, (g i).Monic)
    (hinj : Function.Injective g) :
    Fintype.card {i : ι // (g i).natDegree = 1} = 5 := by
  let e := Equiv.ofBijective (linearFactorRoot g)
    ⟨linear_root_injective g hmonic hinj,
      linear_root_surjective g hfactor hirr hmonic⟩
  simpa using Fintype.card_congr e

set_option maxRecDepth 4000 in
private theorem sum_x_125
    {ι : Type*} [Fintype ι] (g : ι → (ZMod 5)[X])
    (hfactor : X ^ (Nat.card (ZMod 5)) ^ 3 - X = ∏ i, g i)
    (hmonic : ∀ i, (g i).Monic) :
    ∑ i, (g i).natDegree = 125 := by
  rw [← Polynomial.natDegree_prod_of_monic Finset.univ g
    (fun i _ ↦ hmonic i), ← hfactor]
  calc
    (X ^ (Nat.card (ZMod 5)) ^ 3 - X : (ZMod 5)[X]).natDegree = 5 ^ 3 := by
      rw [show Nat.card (ZMod 5) = 5 by norm_num]
      exact FiniteField.X_pow_card_pow_sub_X_natDegree_eq
        (K' := ZMod 5) (p := 5) (n := 3) (by decide) (by decide)
    _ = 125 := by norm_num

private theorem card_125_sub
    {ι : Type*} [Fintype ι] (g : ι → (ZMod 5)[X])
    (hfactor : X ^ (Nat.card (ZMod 5)) ^ 3 - X = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i)) (hmonic : ∀ i, (g i).Monic)
    (hlinear : Fintype.card {i : ι // (g i).natDegree = 1} = 5) :
    Fintype.card {i : ι // (g i).natDegree = 3} = 40 := by
  classical
  let linear : Finset ι := Finset.univ.filter fun i ↦ (g i).natDegree = 1
  let cubic : Finset ι := Finset.univ.filter fun i ↦ (g i).natDegree = 3
  have hnotlinear : Finset.univ.filter (fun i ↦ ¬(g i).natDegree = 1) = cubic := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cubic]
    rcases factor_or_three g hfactor hirr i with hi | hi
    · simp [hi]
    · simp [hi]
  have hsumLinear : ∑ i ∈ linear, (g i).natDegree = linear.card := by
    calc
      ∑ i ∈ linear, (g i).natDegree = ∑ _i ∈ linear, 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      _ = linear.card := by simp
  have hsumCubic : ∑ i ∈ cubic, (g i).natDegree = 3 * cubic.card := by
    calc
      ∑ i ∈ cubic, (g i).natDegree = ∑ _i ∈ cubic, 3 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      _ = 3 * cubic.card := by simp [Nat.mul_comm]
  have hsum : linear.card + 3 * cubic.card = 125 := by
    calc
      linear.card + 3 * cubic.card =
          (∑ i ∈ linear, (g i).natDegree) +
            ∑ i ∈ cubic, (g i).natDegree := by rw [hsumLinear, hsumCubic]
      _ = ∑ i, (g i).natDegree := by
        rw [← hnotlinear]
        exact Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun i ↦ (g i).natDegree = 1) (fun i ↦ (g i).natDegree)
      _ = 125 := sum_x_125 g hfactor hmonic
  have hlinearCard : linear.card = 5 := by
    simpa [linear, Fintype.card_subtype] using hlinear
  have hcubicCard : cubic.card =
      Fintype.card {i : ι // (g i).natDegree = 3} := by
    simp [cubic, Fintype.card_subtype]
  rw [hlinearCard] at hsum
  rw [← hcubicCard]
  omega

/-- Milne's small example in Remark 8.29: in any factorization of
`X^125 - X` over `F₅` into distinct monic irreducibles, there are five
linear factors and forty cubic factors.

The count does not use a polynomial-factorization computation.  Linear
factors are identified with the five elements of `F₅`; every other factor
has degree three by the preceding theorem; and comparison of total degrees
gives the cubic count. -/
theorem x_125_sub
    {ι : Type*} [Fintype ι]
    (g : ι → (ZMod 5)[X])
    (hfactor : X ^ (Nat.card (ZMod 5)) ^ 3 - X = ∏ i, g i)
    (hirr : ∀ i, Irreducible (g i))
    (hmonic : ∀ i, (g i).Monic)
    (hinj : Function.Injective g) :
    Fintype.card {i : ι // (g i).natDegree = 1} = 5 ∧
      Fintype.card {i : ι // (g i).natDegree = 3} = 40 := by
  have hlinear := card_x_125
    g hfactor hirr hmonic hinj
  exact ⟨hlinear,
    card_125_sub g hfactor hirr hmonic hlinear⟩

end Submission.NumberTheory.Milne
