import Towers.ClassField.CrossedProducts.CohomologyRestriction

/-!
# Restriction in multiplicative Galois cohomology

For a field tower `K → L → E`, every `L`-automorphism of `E` is also a
`K`-automorphism.  Pulling cocycles back along this inclusion gives the
restriction map `H²(E/K) → H²(E/L)` used in the local invariant theorem.
-/

namespace Towers.CField.CProduca

noncomputable section

universe u

attribute [local instance] Units.mulDistribMulActionRight

variable (K L E : Type u) [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

/-- Regard an automorphism over the intermediate field as an automorphism
over the base field. -/
def galoisTowerInclusion : Gal(E/L) →* Gal(E/K) where
  toFun sigma := sigma.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem galois_tower_inclusion (sigma : Gal(E/L)) (x : E) :
    galoisTowerInclusion K L E sigma x = sigma x :=
  rfl

/-- Restriction from `H²(E/K)` to `H²(E/L)` in normalized multiplicative
Galois cohomology. -/
def galoisHRestriction :
    MHTwo Gal(E/K) Eˣ →* MHTwo Gal(E/L) Eˣ :=
  MHTwo.restrictionHom (galoisTowerInclusion K L E) (by
    intro sigma x
    rfl)

@[simp]
theorem galois_restriction_mk
    (c : NMCocycl₂ (G := Gal(E/K)) (M := Eˣ)) :
    galoisHRestriction K L E (MHTwo.mk c) =
      MHTwo.mk
        (NMCocycl₂.restrict (galoisTowerInclusion K L E)
          (by intro sigma x; rfl) c) :=
  rfl

/-- Restriction in Galois cohomology is transitive through an intermediate
field. -/
theorem h_restriction_trans
    (M : Type u) [Field M]
    [Algebra K M] [Algebra L M] [Algebra M E]
    [IsScalarTower K L M] [IsScalarTower K M E]
    [IsScalarTower L M E]
    (x : MHTwo Gal(E/K) Eˣ) :
    galoisHRestriction L M E (galoisHRestriction K L E x) =
      galoisHRestriction K M E x := by
  induction x using Quotient.inductionOn with
  | _ c => rfl

end

end Towers.CField.CProduca
