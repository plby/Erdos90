import Towers.ClassField.Shifting.AdditiveHomZero
import Towers.ClassField.Shifting.TateZero
import Towers.ClassField.Shifting.CyclicTateShape

/-!
# Milne, Class Field Theory, Lemma III.2.5

This file proves the explicit final calculation in Milne's proof:
the Herbrand quotient of the trivial integral representation of a finite
cyclic group is the order of the group.
-/

namespace Towers.CField.LClass

open CategoryTheory Representation
open Shifting

noncomputable section

variable {G : Type} [CommGroup G] [Fintype G]

/-- Finiteness of `H¹(G,ℤ)`, obtained from its vanishing. -/
@[reducible]
private noncomputable def h1Trivial (G : Type) [CommGroup G] [Fintype G] :
    Finite (groupCohomology (Rep.trivial ℤ G ℤ) 1) := by
  letI : Subsingleton (groupCohomology (Rep.trivial ℤ G ℤ) 1) :=
    ModuleCat.subsingleton_of_isZero (cohomology_trivial_int G)
  infer_instance

/-- Finiteness of `H²(G,ℤ)` for a chosen cyclic generator. -/
@[reducible]
private noncomputable def h2Trivial
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (groupCohomology (Rep.trivial ℤ G ℤ) 2) := by
  let e₀ := tateCohomologyTrivial G
  letI : Finite (tateCohomologyZero (Rep.trivial ℤ G ℤ)) :=
    Finite.of_equiv (ZMod (Fintype.card G)) e₀.symm.toEquiv
  exact Finite.of_equiv (tateCohomologyZero (Rep.trivial ℤ G ℤ))
    (tateCohomologyTwo
      (Rep.trivial ℤ G ℤ) g hg).toEquiv

/-- The Herbrand quotient of the trivial integral representation, with the
finiteness proofs supplied by cyclicity. -/
noncomputable def trivialIntHerbrand
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) : ℚˣ := by
  letI := h1Trivial G
  letI := h2Trivial g hg
  exact herbrandQuotient (Rep.trivial ℤ G ℤ)

/-- **Lemma III.2.5, the calculation `h(ℤ) = |G|`.** -/
theorem herbrand_trivial_int
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    (trivialIntHerbrand g hg : ℚ) = Fintype.card G := by
  letI : Subsingleton (groupCohomology (Rep.trivial ℤ G ℤ) 1) :=
    ModuleCat.subsingleton_of_isZero (cohomology_trivial_int G)
  letI := h1Trivial G
  letI := h2Trivial g hg
  let e₀ := tateCohomologyTrivial G
  let e₂ := tateCohomologyTwo
    (Rep.trivial ℤ G ℤ) g hg
  have hcard₂ : Nat.card (groupCohomology (Rep.trivial ℤ G ℤ) 2) =
      Fintype.card G := by
    calc
      Nat.card (groupCohomology (Rep.trivial ℤ G ℤ) 2) =
          Nat.card (tateCohomologyZero (Rep.trivial ℤ G ℤ)) :=
        Nat.card_congr e₂.symm.toEquiv
      _ = Nat.card (ZMod (Fintype.card G)) := Nat.card_congr e₀.toEquiv
      _ = Fintype.card G := Nat.card_zmod _
  simp [trivialIntHerbrand, herbrandQuotient,
    card_unit_val, hcard₂]

end

end Towers.CField.LClass
