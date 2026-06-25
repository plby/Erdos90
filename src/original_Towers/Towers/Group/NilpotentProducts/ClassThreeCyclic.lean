import Towers.Group.NilpotentProducts.GeneralCollection
import Towers.Group.NilpotentProducts.CyclicProducts

/-!
# Class-three formulas in Struik's cyclic nilpotent products

These statements specialize the arbitrary-group collection formulas to
the groups `F/F₄` that occur throughout sections 2 and 3 of the paper.
-/

namespace Struik
namespace P1960

open Towers
open Towers.Edmonton
open Towers.TCTex
open scoped commutatorElement

universe u

variable {ι : Type u}

/-- Lemma 2 holds in every fourth nilpotent product of cyclic groups. -/
theorem cyclic_products_nilpotent
    (order : ι → ℕ)
    (a b : NilpotentCyclicProduct order 4)
    (r s : ℤ) :
    hallCommutator (a ^ r) (b ^ s) =
        hallCommutator a b ^ (r * s) *
          hallTripleCommutator a b a ^ (s * Ring.choose r 2) *
            hallTripleCommutator a b b ^ (r * Ring.choose s 2) ∧
      hallCommutator (b ^ r) (a ^ s) =
        hallCommutator a b ^ (-(r * s)) *
          hallTripleCommutator a b a ^ (-(r * Ring.choose s 2)) *
            hallTripleCommutator a b b ^ (-(s * Ring.choose r 2)) :=
  of_classThree
    (nilpotent_four_bot order)
    a b r s

/-- Equation (28), first formula, in a fourth nilpotent product. -/
theorem cyclic_products_four
    (order : ι → ℕ)
    (a b : NilpotentCyclicProduct order 4) :
    hallCommutator (a ^ (2 : ℤ)) b =
      hallCommutator a b ^ (2 : ℤ) *
        hallTripleCommutator a b a :=
  generalCollectionFirst
    (nilpotent_four_bot order) a b

/-- Equation (28), second formula, in a fourth nilpotent product. -/
theorem products_nilpotent_four
    (order : ι → ℕ)
    (a b : NilpotentCyclicProduct order 4) :
    hallCommutator a (b ^ (2 : ℤ)) =
      hallCommutator a b ^ (2 : ℤ) *
        hallTripleCommutator a b b :=
  generalCollectionSecond
    (nilpotent_four_bot order) a b

/-- Equation (24) for a canonical cyclic generator of order two. -/
theorem cyclicProductsNilpotent
    (order : ι → ℕ) (i : ι)
    (hi : order i = 2)
    (a : NilpotentCyclicProduct order 4) :
    1 =
      hallCommutator a (nilpotentCyclicGenerator order 4 i) ^ (2 : ℤ) *
        hallTripleCommutator a (nilpotentCyclicGenerator order 4 i)
          (nilpotentCyclicGenerator order 4 i) := by
  apply generalCollection
  simpa [hi] using
    nilpotent_cyclic_generator order 4 i

end P1960
end Struik
