import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Submission.NumberTheory.Cyclotomic.PrimeAutomorphismGroups
import Submission.ClassField.CrossedProducts.TensorRightCongr

/-!
# Chapter VII, Section 7: cyclic cyclotomic splitting fields

Lemma 7.3 constructs a totally complex cyclic cyclotomic extension with
prescribed divisibility of finitely many local degrees.  The completion
degrees are expressed concretely by `prime_statement_bridges`; the
algebraic ingredients for the cyclotomic construction available in Mathlib
and the Milne development are recorded here:

* cyclotomic extensions are Galois;
* odd-prime-power cyclotomic Galois groups are cyclic;
* the degree of a rational cyclotomic field is Euler's totient;
* products of finite cyclic groups of coprime orders are cyclic;
* splitting persists up a field tower, which is the final algebraic step in
  the second concrete restatement after Proposition 7.2.

The remaining arithmetic input is the prime-power local-degree growth and
its assembly into the cyclic compositum used in the printed proof.
-/

namespace Submission.CField.CBrauer

noncomputable section

universe u

/-- The Galois part of the definition of a cyclotomic extension used in
Lemma 7.3. -/
theorem cyclotomic_isGalois
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [IsCyclotomicExtension {n} K L] :
    IsGalois K L :=
  IsCyclotomicExtension.isGalois {n} K L

/-- **Lemma VII.7.3, odd-prime-power cyclicity input.** An odd-prime-power
cyclotomic extension has cyclic automorphism group. -/
theorem odd_aut_cyclic
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsCyclotomicExtension {p ^ r} K L] :
    IsCyclic (L ≃ₐ[K] L) :=
  Submission.NumberTheory.Milne.exercise_six_aut
    (p := p) (r := r) hp hp2 K L

/-- The degree computation for the full rational cyclotomic field appearing
in the proof of Lemma 7.3. -/
theorem rational_finrank_totient
    (n : ℕ) [NeZero n]
    (L : Type u) [Field L] [NumberField L]
    [IsCyclotomicExtension {n} ℚ L] :
    Module.finrank ℚ L = n.totient :=
  IsCyclotomicExtension.Rat.finrank n L

/-- The prime-power specialization of the cyclotomic degree formula used in
the construction in Lemma 7.3. -/
theorem rational_cyclotomic_finrank
    {p r : ℕ} (hp : p.Prime) (hr : 0 < r)
    (L : Type u) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    Module.finrank ℚ L = p ^ (r - 1) * (p - 1) := by
  letI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  calc
    Module.finrank ℚ L = (p ^ r).totient :=
      IsCyclotomicExtension.Rat.finrank (p ^ r) L
    _ = p ^ (r - 1) * (p - 1) := Nat.totient_prime_pow hp hr

/-- The group-theoretic product step in Lemma 7.3: cyclic groups of coprime
finite orders have cyclic product. -/
theorem cyclic_coprime_card
    (G H : Type u) [Group G] [Group H] [Finite G] [Finite H]
    [IsCyclic G] [IsCyclic H]
    (hcoprime : (Nat.card G).Coprime (Nat.card H)) :
    IsCyclic (G × H) :=
  Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, hcoprime⟩

/-- The tower step behind the second concrete statement of the section:
once a cyclic cyclotomic extension contains a splitting field, it also splits
the algebra.  Cyclicity and cyclotomicity are included to expose the exact
shape needed by Proposition 7.2. -/
theorem split_cyclic_tower
    (K E L A : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Ring A] [Algebra K A]
    {n : ℕ} [IsCyclotomicExtension {n} K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (hE : BGroups.ISBy K E A) :
    BGroups.ISBy K L A :=
  CProduca.ISBy.tower K E L A hE

end

end Submission.CField.CBrauer
