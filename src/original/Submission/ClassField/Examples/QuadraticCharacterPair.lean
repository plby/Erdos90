import Submission.ClassField.Examples.OddSplitsOrder

/-!
# Class Field Theory, Exercise 0.15

The global Artin map and ray class groups needed for the full exercise are not
yet available.  This file records the elementary quadratic-character
calculation underlying part (b).  For primes away from `2` and `5`, the two
characters belonging to `Q(i)` and `Q(sqrt(-5))` are determined by the prime
modulo `20`, and their four possible pairs distinguish the four elements of
the biquadratic Galois group.
-/

namespace Submission.CField.Examples

/-- The two quadratic characters cutting out `Q(i)` and `Q(sqrt(-5))`. -/
def quadraticCharacterPair (p : ℕ) [Fact p.Prime] : ℤ × ℤ :=
  (legendreSym p (-1), legendreSym p (-5))

/-- The character pair in Exercise 0.15 is constant on odd-prime residue
classes modulo `20`. -/
theorem quadratic_character_twenty
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≡ q [MOD 20]) :
    quadraticCharacterPair p =
      quadraticCharacterPair q := by
  apply Prod.ext
  · simpa [quadraticCharacterPair] using
      legendre_sym_abs (-1) hp2 hq2 (by
      simpa using hpq.of_dvd (by norm_num : 4 * (-1 : ℤ).natAbs ∣ 20))
  · simpa [quadraticCharacterPair] using
      legendre_sym_abs (-5) hp2 hq2 (by
      simpa using hpq)

private theorem legendre_neg_twenty
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 20 = 1 ∨ p % 20 = 9 ∨ p % 20 = 13 ∨ p % 20 = 17) :
    legendreSym p (-1) = 1 := by
  rw [legendreSym.at_neg_one hp2]
  apply ZMod.χ₄_nat_one_mod_four
  rcases hp with hp | hp | hp | hp <;> omega

private theorem legendre_sym_twenty
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 11 ∨ p % 20 = 19) :
    legendreSym p (-1) = -1 := by
  rw [legendreSym.at_neg_one hp2]
  apply ZMod.χ₄_nat_three_mod_four
  rcases hp with hp | hp | hp | hp <;> omega

private theorem legendre_sym_five
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 20 = 1 ∨ p % 20 = 9 ∨ p % 20 = 11 ∨ p % 20 = 19) :
    legendreSym p 5 = 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [show legendreSym p (5 : ℤ) = legendreSym 5 (p : ℤ) by
    exact legendreSym.quadratic_reciprocity_one_mod_four
      (p := 5) (q := p) (by norm_num) hp2]
  rw [legendreSym.mod]
  rcases hp with hp | hp | hp | hp
  all_goals
    have hp5 : p % 5 = 1 ∨ p % 5 = 4 := by omega
    rcases hp5 with hp5 | hp5
    · rw [show (p : ℤ) % (5 : ℕ) = (p % 5 : ℕ) by omega, hp5]
      decide
    · rw [show (p : ℤ) % (5 : ℕ) = (p % 5 : ℕ) by omega, hp5]
      decide

private theorem legendre_five_twenty
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 13 ∨ p % 20 = 17) :
    legendreSym p 5 = -1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [show legendreSym p (5 : ℤ) = legendreSym 5 (p : ℤ) by
    exact legendreSym.quadratic_reciprocity_one_mod_four
      (p := 5) (q := p) (by norm_num) hp2]
  rw [legendreSym.mod]
  rcases hp with hp | hp | hp | hp
  all_goals
    have hp5 : p % 5 = 2 ∨ p % 5 = 3 := by omega
    rcases hp5 with hp5 | hp5
    · rw [show (p : ℤ) % (5 : ℕ) = (p % 5 : ℕ) by omega, hp5]
      decide
    · rw [show (p : ℤ) % (5 : ℕ) = (p % 5 : ℕ) by omega, hp5]
      decide

private theorem legendre_neg_five
    (p : ℕ) [Fact p.Prime] :
    legendreSym p (-5) = legendreSym p (-1) * legendreSym p 5 := by
  simpa using legendreSym.mul p (-1) 5

/-- The identity element: primes congruent to `1` or `9` modulo `20` split
in both quadratic subextensions. -/
theorem character_pair_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 20 = 1 ∨ p % 20 = 9) :
    quadraticCharacterPair p = (1, 1) := by
  have hnegOne := legendre_neg_twenty hp2
    (hp.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
  have hfive := legendre_sym_five hp2
    (hp.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
  rw [quadraticCharacterPair, legendre_neg_five, hnegOne, hfive]
  norm_num

/-- Primes congruent to `3` or `7` modulo `20` are nonsquares for `-1` but
squares for `-5`. -/
theorem character_neg_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 20 = 3 ∨ p % 20 = 7) :
    quadraticCharacterPair p = (-1, 1) := by
  have hnegOne := legendre_sym_twenty hp2
    (hp.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
  have hfive := legendre_five_twenty hp2
    (hp.elim Or.inl (fun h ↦ Or.inr (Or.inl h)))
  rw [quadraticCharacterPair, legendre_neg_five, hnegOne, hfive]
  norm_num

/-- Primes congruent to `13` or `17` modulo `20` are squares for `-1` but
nonsquares for `-5`. -/
theorem character_one_neg
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 20 = 13 ∨ p % 20 = 17) :
    quadraticCharacterPair p = (1, -1) := by
  have hnegOne := legendre_neg_twenty hp2
    (hp.elim (fun h ↦ Or.inr (Or.inr (Or.inl h)))
      (fun h ↦ Or.inr (Or.inr (Or.inr h))))
  have hfive := legendre_five_twenty hp2
    (hp.elim (fun h ↦ Or.inr (Or.inr (Or.inl h)))
      (fun h ↦ Or.inr (Or.inr (Or.inr h))))
  rw [quadraticCharacterPair, legendre_neg_five, hnegOne, hfive]
  norm_num

/-- The remaining two prime classes, `11` and `19` modulo `20`, are
nonsquares for both `-1` and `-5`. -/
theorem character_pair_neg
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 20 = 11 ∨ p % 20 = 19) :
    quadraticCharacterPair p = (-1, -1) := by
  have hnegOne := legendre_sym_twenty hp2
    (hp.elim (fun h ↦ Or.inr (Or.inr (Or.inl h)))
      (fun h ↦ Or.inr (Or.inr (Or.inr h))))
  have hfive := legendre_sym_five hp2
    (hp.elim (fun h ↦ Or.inr (Or.inr (Or.inl h)))
      (fun h ↦ Or.inr (Or.inr (Or.inr h))))
  rw [quadraticCharacterPair, legendre_neg_five, hnegOne, hfive]
  norm_num

/-- Every rational prime away from `2` and `5` lies in one of the four
quadratic-character cases above. -/
theorem characterPair_classification
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((p % 20 = 1 ∨ p % 20 = 9) ∧
        quadraticCharacterPair p = (1, 1)) ∨
      ((p % 20 = 3 ∨ p % 20 = 7) ∧
        quadraticCharacterPair p = (-1, 1)) ∨
      ((p % 20 = 13 ∨ p % 20 = 17) ∧
        quadraticCharacterPair p = (1, -1)) ∨
      ((p % 20 = 11 ∨ p % 20 = 19) ∧
        quadraticCharacterPair p = (-1, -1)) := by
  have hpOdd : p % 2 = 1 :=
    (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out : Nat.Prime p)).mpr hp2
  have hpModFive : p % 5 ≠ 0 := by
    intro hp0
    have hdiv : 5 ∣ p := Nat.dvd_of_mod_eq_zero hp0
    have hEq : 5 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_five (Fact.out : Nat.Prime p)).mp hdiv
    exact hp5 hEq.symm
  have hclasses :
      p % 20 = 1 ∨ p % 20 = 3 ∨ p % 20 = 7 ∨ p % 20 = 9 ∨
        p % 20 = 11 ∨ p % 20 = 13 ∨ p % 20 = 17 ∨ p % 20 = 19 := by
    omega
  rcases hclasses with h | h | h | h | h | h | h | h
  · exact Or.inl ⟨Or.inl h, character_pair_one hp2 (Or.inl h)⟩
  · exact Or.inr <| Or.inl
      ⟨Or.inl h, character_neg_one hp2 (Or.inl h)⟩
  · exact Or.inr <| Or.inl
      ⟨Or.inr h, character_neg_one hp2 (Or.inr h)⟩
  · exact Or.inl ⟨Or.inr h, character_pair_one hp2 (Or.inr h)⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨Or.inl h, character_pair_neg hp2 (Or.inl h)⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨Or.inl h, character_one_neg hp2 (Or.inl h)⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨Or.inr h, character_one_neg hp2 (Or.inr h)⟩
  · exact Or.inr <| Or.inr <| Or.inr
      ⟨Or.inr h, character_pair_neg hp2 (Or.inr h)⟩

/-- The trivial character pair is precisely simultaneous splitting in the
two quadratic orders from Exercise 0.15. -/
theorem splits_both_character
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    (OddSplitsQuadratic (-1) p ∧
        OddSplitsQuadratic (-5) p) ↔
      quadraticCharacterPair p = (1, 1) := by
  have hpNegOne : ¬(p : ℤ) ∣ (-1 : ℤ) := by
    intro hdiv
    have hpOne : p ∣ 1 := by exact_mod_cast (dvd_neg.mp hdiv)
    exact (Fact.out : Nat.Prime p).not_dvd_one hpOne
  have hpNegFive : ¬(p : ℤ) ∣ (-5 : ℤ) := by
    intro hdiv
    have hpFiveInt : (p : ℤ) ∣ (5 : ℤ) := dvd_neg.mp hdiv
    have hpFive : p ∣ 5 := by exact_mod_cast hpFiveInt
    exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_five).mp hpFive)
  rw [odd_splits_legendre (-1) p hp2 hpNegOne,
    odd_splits_legendre (-5) p hp2 hpNegFive,
    quadraticCharacterPair]
  simp

/-! ### The finite quotient underlying part (c) -/

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The two quadratic characters on the ray residue group modulo `20`.

The first component is the character modulo `4` belonging to `Q(i)`, while
the second is the quadratic character modulo `5`.  Their product recovers the
character belonging to `Q(sqrt(-5))`, so this pair contains the same
information as the pair used above. -/
def rayCharacter : (ZMod 20)ˣ →* ℤˣ × ℤˣ :=
  ((ZMod.χ₄.toUnitHom.comp (ZMod.unitsMap (by norm_num : 4 ∣ 20))).prod
    ((quadraticChar (ZMod 5)).toUnitHom.comp
      (ZMod.unitsMap (by norm_num : 5 ∣ 20))))

/-- The character pair modulo `20` assumes all four possible sign pairs. -/
theorem rayCharacter_surjective :
    Function.Surjective rayCharacter := by
  decide

/-- Its kernel consists of the two ray residue classes `1` and `9`. -/
theorem ray_character_ker (u : (ZMod 20)ˣ) :
    u ∈ rayCharacter.ker ↔ u.val = 1 ∨ u.val = 9 := by
  decide +revert

/-- The corresponding quotient of the ray residue group modulo `20` is the
four-element sign-pair group. -/
noncomputable def rayCharacterEquiv :
    (ZMod 20)ˣ ⧸ rayCharacter.ker ≃* ℤˣ × ℤˣ :=
  QuotientGroup.quotientKerEquivOfSurjective rayCharacter
    rayCharacter_surjective

end Submission.CField.Examples
