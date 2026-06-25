import Mathlib.FieldTheory.Finite.Basic
import Towers.ClassField.CrossedProducts.GaloisRestriction

/-!
# Restriction of arithmetic Frobenius in finite-field towers

The residue-field calculation in Milne's Proposition III.1.8 is that
Frobenius over an intermediate finite field is the corresponding power of
Frobenius over the base field.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open IsLocalRing

attribute [local instance] Ideal.Quotient.field

/-- If the intermediate field has `q ^ f` elements, its arithmetic
Frobenius on the top field is the `f`-th power of arithmetic Frobenius over
the field with `q` elements. -/
theorem frobenius_restrict_scalars
    (k l E : Type u) [Field k] [Field l] [Field E]
    [Fintype k] [Fintype l]
    [Algebra k l] [Algebra k E] [Algebra l E] [IsScalarTower k l E]
    [Algebra.IsAlgebraic k E] [Algebra.IsAlgebraic l E]
    (f : ℕ) (hcard : Fintype.card l = Fintype.card k ^ f) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic l E).restrictScalars k =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ f := by
  ext x
  change x ^ Fintype.card l =
    (FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ f) x
  rw [hcard, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- In a finite-field tower the exponent in the preceding restriction law
is the degree of the intermediate residue extension. -/
theorem restrict_scalars_finrank
    (k l E : Type u) [Field k] [Field l] [Field E]
    [Fintype k] [Fintype l]
    [Algebra k l] [Algebra k E] [Algebra l E] [IsScalarTower k l E]
    [FiniteDimensional k l]
    [Algebra.IsAlgebraic k E] [Algebra.IsAlgebraic l E] :
    (FiniteField.frobeniusAlgEquivOfAlgebraic l E).restrictScalars k =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E ^
        Module.finrank k l := by
  apply frobenius_restrict_scalars k l E
  exact Module.card_eq_pow_finrank

/-- Naturality of reduction-induced Galois equivalences in a group tower.
The statement isolates the only property of the local integral models used
in the proof: both residue actions are obtained by reducing the same action
on the top ring. -/
theorem residue_tower_inclusion
    {A B C GA GB : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra (ResidueField A) (ResidueField B)]
    [Algebra (ResidueField A) (ResidueField C)]
    [Algebra (ResidueField B) (ResidueField C)]
    [IsScalarTower (ResidueField A) (ResidueField B) (ResidueField C)]
    [Group GA] [Group GB]
    [MulSemiringAction GA C] [MulSemiringAction GB C]
    (incl : GB →* GA)
    (eA : GA ≃* Gal(ResidueField C/ResidueField A))
    (eB : GB ≃* Gal(ResidueField C/ResidueField B))
    (hreduceA : ∀ (g : GA) (c : C),
      eA g (residue C c) = residue C (g • c))
    (hreduceB : ∀ (g : GB) (c : C),
      eB g (residue C c) = residue C (g • c))
    (haction : ∀ (g : GB) (c : C), incl g • c = g • c)
    (g : GB) :
    eA (incl g) = (eB g).restrictScalars (ResidueField A) := by
  ext x
  obtain ⟨c, rfl⟩ := residue_surjective x
  change eA (incl g) (residue C c) = eB g (residue C c)
  rw [hreduceA, hreduceB, haction]

/-- Frobenius lifts through compatible reduction equivalences satisfy the
same power restriction law as finite-field Frobenius. -/
theorem frobenius_tower_inclusion
    {A B C GA GB : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra (ResidueField A) (ResidueField B)]
    [Algebra (ResidueField A) (ResidueField C)]
    [Algebra (ResidueField B) (ResidueField C)]
    [IsScalarTower (ResidueField A) (ResidueField B) (ResidueField C)]
    [Fintype (ResidueField A)] [Fintype (ResidueField B)]
    [Algebra.IsAlgebraic (ResidueField A) (ResidueField C)]
    [Algebra.IsAlgebraic (ResidueField B) (ResidueField C)]
    [Group GA] [Group GB]
    [MulSemiringAction GA C] [MulSemiringAction GB C]
    (incl : GB →* GA)
    (eA : GA ≃* Gal(ResidueField C/ResidueField A))
    (eB : GB ≃* Gal(ResidueField C/ResidueField B))
    (hreduceA : ∀ (g : GA) (c : C),
      eA g (residue C c) = residue C (g • c))
    (hreduceB : ∀ (g : GB) (c : C),
      eB g (residue C c) = residue C (g • c))
    (haction : ∀ (g : GB) (c : C), incl g • c = g • c)
    (f : ℕ)
    (hcard : Fintype.card (ResidueField B) =
      Fintype.card (ResidueField A) ^ f) :
    incl (eB.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
        (ResidueField B) (ResidueField C))) =
      (eA.symm (FiniteField.frobeniusAlgEquivOfAlgebraic
        (ResidueField A) (ResidueField C))) ^ f := by
  apply eA.injective
  rw [residue_tower_inclusion incl eA eB
      hreduceA hreduceB haction,
    eB.apply_symm_apply,
    frobenius_restrict_scalars _ _ _ f hcard,
    map_pow, eA.apply_symm_apply]

end

end Towers.CField.LBrauer
