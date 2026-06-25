import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Towers.Group.HallBasic.Word

/-!
# Recursive coefficient splitting for Hall word polynomials

Every monomial in the associative polynomial of a Hall tree has the tree's
weight.  Therefore multiplication of two such homogeneous polynomials has a
unique word split: the left factor must occupy the prefix whose length is the
left tree's weight.

This file records the resulting coefficient formula and the corresponding
binary-commutator recursion.  These identities are the algebraic core of a
recursive Hall leading-word proof.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace HallTree

universe u

variable {α : Type u}

/-- Prefix of a free-monoid word of the requested length. -/
def wordPrefix
    (n : ℕ)
    (word : FreeMonoid α) :
    FreeMonoid α :=
  FreeMonoid.ofList (word.toList.take n)

/-- Suffix remaining after removal of the requested prefix length. -/
def wordSuffix
    (n : ℕ)
    (word : FreeMonoid α) :
    FreeMonoid α :=
  FreeMonoid.ofList (word.toList.drop n)

/-- Splitting a free-monoid word into a prefix and suffix recovers the word. -/
@[simp] theorem word_prefix_suffix
    (n : ℕ)
    (word : FreeMonoid α) :
    wordPrefix n word * wordSuffix n word = word := by
  apply FreeMonoid.toList.injective
  simp [wordPrefix, wordSuffix]

/-- Below the word length, the requested prefix has exactly that length. -/
@[simp] theorem wordPrefix_length
    {n : ℕ}
    {word : FreeMonoid α}
    (hn : n ≤ word.length) :
    (wordPrefix n word).length = n := by
  change (word.toList.take n).length = n
  change n ≤ word.toList.length at hn
  exact List.length_take_of_le hn

/--
The support of two homogeneous Hall-tree polynomials has a unique
concatenation split at the first tree's weight.
-/
theorem associative_unique_length
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (leftWord rightWord : FreeMonoid α)
    (hleft : leftWord.length = u.weight) :
    UniqueMul
      (u.associativeWordPolynomial R).support
      (v.associativeWordPolynomial R).support
      leftWord rightWord := by
  intro left' right' hleft' hright' heq
  have hleftLength :=
    associative_word_length R u hleft'
  have hlistEq :
      left'.toList ++ right'.toList =
        leftWord.toList ++ rightWord.toList := by
    simpa only [FreeMonoid.toList_mul] using
      congrArg FreeMonoid.toList heq
  have hprefixLength :
      left'.toList.length = leftWord.toList.length := by
    change left'.length = leftWord.length
    exact hleftLength.trans hleft.symm
  rcases List.append_inj hlistEq hprefixLength with
    ⟨hleftEq, hrightEq⟩
  exact
    ⟨FreeMonoid.toList.injective hleftEq,
      FreeMonoid.toList.injective hrightEq⟩

/--
At a concatenated word whose prefix has the first tree's weight, the product
coefficient is the product of the two child coefficients.
-/
theorem associative_mul_concat
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (leftWord rightWord : FreeMonoid α)
    (hleft : leftWord.length = u.weight) :
    (u.associativeWordPolynomial R * v.associativeWordPolynomial R)
        (leftWord * rightWord) =
      u.associativeWordPolynomial R leftWord *
        v.associativeWordPolynomial R rightWord :=
  MonoidAlgebra.mul_apply_mul_eq_mul_of_uniqueMul
    (associative_unique_length
      R u v leftWord rightWord hleft)

/--
At a word of the product's homogeneous degree, multiplication splits exactly
at the first tree's weight.
-/
theorem associative_prefix_suffix
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (word : FreeMonoid α)
    (hword : word.length = u.weight + v.weight) :
    (u.associativeWordPolynomial R * v.associativeWordPolynomial R) word =
      u.associativeWordPolynomial R (wordPrefix u.weight word) *
        v.associativeWordPolynomial R (wordSuffix u.weight word) := by
  calc
    _ =
        (u.associativeWordPolynomial R * v.associativeWordPolynomial R)
          (wordPrefix u.weight word * wordSuffix u.weight word) := by
            rw [word_prefix_suffix]
    _ = _ :=
      associative_mul_concat
        R u v (wordPrefix u.weight word) (wordSuffix u.weight word)
        (wordPrefix_length (by omega))

/--
Coefficient recursion for a Hall-tree commutator.  The forward product splits
at the left child's weight and the reverse product splits at the right child's
weight.
-/
theorem associative_commutator_suffix
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (word : FreeMonoid α)
    (hword : word.length = (commutator u v).weight) :
    (commutator u v).associativeWordPolynomial R word =
      u.associativeWordPolynomial R (wordPrefix u.weight word) *
          v.associativeWordPolynomial R (wordSuffix u.weight word) -
        v.associativeWordPolynomial R (wordPrefix v.weight word) *
          u.associativeWordPolynomial R (wordSuffix v.weight word) := by
  rw [associative_word_commutator]
  change
    (u.associativeWordPolynomial R * v.associativeWordPolynomial R) word -
        (v.associativeWordPolynomial R * u.associativeWordPolynomial R) word =
      _
  rw [associative_prefix_suffix
    R u v word (by simpa only [weight_commutator] using hword)]
  rw [associative_prefix_suffix
    R v u word (by
      simpa only [weight_commutator, Nat.add_comm] using hword)]

/--
At a recursively concatenated word, a commutator coefficient is the forward
child-coefficient product minus the reverse-orientation product coefficient.
-/
theorem associative_commutator_concat
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (leftWord rightWord : FreeMonoid α)
    (hleft : leftWord.length = u.weight) :
    (commutator u v).associativeWordPolynomial R (leftWord * rightWord) =
      u.associativeWordPolynomial R leftWord *
          v.associativeWordPolynomial R rightWord -
        (v.associativeWordPolynomial R * u.associativeWordPolynomial R)
          (leftWord * rightWord) := by
  rw [associative_word_commutator]
  change
    (u.associativeWordPolynomial R * v.associativeWordPolynomial R)
          (leftWord * rightWord) -
        (v.associativeWordPolynomial R * u.associativeWordPolynomial R)
          (leftWord * rightWord) =
      _
  rw [associative_mul_concat
    R u v leftWord rightWord hleft]

/--
Signed-unit child pivots recursively give a signed-unit commutator pivot once
the reverse orientation vanishes at the concatenated word.
-/
theorem associative_concat_signed
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (leftWord rightWord : FreeMonoid α)
    (hleft : leftWord.length = u.weight)
    (hu :
      u.associativeWordPolynomial R leftWord = 1 ∨
        u.associativeWordPolynomial R leftWord = -1)
    (hv :
      v.associativeWordPolynomial R rightWord = 1 ∨
        v.associativeWordPolynomial R rightWord = -1)
    (hreverse :
      (v.associativeWordPolynomial R * u.associativeWordPolynomial R)
          (leftWord * rightWord) = 0) :
    (commutator u v).associativeWordPolynomial R (leftWord * rightWord) = 1 ∨
      (commutator u v).associativeWordPolynomial R
          (leftWord * rightWord) = -1 := by
  rw [associative_commutator_concat
    R u v leftWord rightWord hleft, hreverse, sub_zero]
  rcases hu with hu | hu <;> rcases hv with hv | hv <;>
    simp [hu, hv]

/--
A recursively concatenated commutator coefficient vanishes when its forward
child product and its reverse-orientation product both vanish.
-/
theorem associative_concat_zero
    (R : Type*) [CommRing R]
    (u v : HallTree α)
    (leftWord rightWord : FreeMonoid α)
    (hleft : leftWord.length = u.weight)
    (hforward :
      u.associativeWordPolynomial R leftWord = 0 ∨
        v.associativeWordPolynomial R rightWord = 0)
    (hreverse :
      (v.associativeWordPolynomial R * u.associativeWordPolynomial R)
          (leftWord * rightWord) = 0) :
    (commutator u v).associativeWordPolynomial R
        (leftWord * rightWord) = 0 := by
  rw [associative_commutator_concat
    R u v leftWord rightWord hleft, hreverse, sub_zero]
  rcases hforward with hforward | hforward <;> simp [hforward]

end HallTree
end Towers
