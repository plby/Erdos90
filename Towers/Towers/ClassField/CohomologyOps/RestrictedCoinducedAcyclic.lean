import Towers.ClassField.CohomologyOps.DimensionShiftingIso

/-!
# Restriction of a module coinduced from the trivial subgroup

For an arbitrary subgroup `H ≤ G`, restriction to `H` of a representation
coinduced from the trivial subgroup of `G` is again coinduced from the trivial
subgroup of `H`. The coefficient module consists of functions on the set of
left cosets `G / H`.

This is the unconditional acyclicity input in Milne's dimension-shifting proof
of Proposition II.1.34. Neither finiteness of `G` nor finite index or normality
of `H` is needed.
-/

namespace Towers.CField.COps

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Coordinates

variable (H : Subgroup G)

/-- The `H`-coordinate of `g` relative to the representative selected by
`Quotient.out` for the left coset of `g`. -/
noncomputable def unrestrictedCosetCoordinate (g : G) : H :=
  ⟨(Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹ * g,
    QuotientGroup.leftRel_apply.mp
      (Quotient.eq'.mp (Quotient.out_eq' (QuotientGroup.mk g : G ⧸ H)))⟩

theorem unrestricted_coset_coordinate (g : G) :
    Quotient.out (QuotientGroup.mk g : G ⧸ H) *
        unrestrictedCosetCoordinate H g = g := by
  simp [unrestrictedCosetCoordinate]

theorem unrestricted_coset_representative
    (q : G ⧸ H) (h : H) :
    unrestrictedCosetCoordinate H (Quotient.out q * h) = h := by
  apply Subtype.ext
  simp [unrestrictedCosetCoordinate, QuotientGroup.mk_mul_of_mem]

/-- Multiplication gives coordinates consisting of a selected left-coset
representative followed by an element of `H`. -/
noncomputable def unrestrictedRightCoset : G ≃ (G ⧸ H) × H where
  toFun g :=
    ((QuotientGroup.mk g : G ⧸ H), unrestrictedCosetCoordinate H g)
  invFun qh := Quotient.out qh.1 * qh.2
  left_inv := unrestricted_coset_coordinate H
  right_inv qh := by
    rcases qh with ⟨q, h⟩
    apply Prod.ext
    · simp [QuotientGroup.mk_mul_of_mem]
    · exact unrestricted_coset_representative H q h

end Coordinates

section RestrictedCoinduction

variable (H : Subgroup G)

/-- The coefficient representation over the trivial subgroup of `H`: one
copy of the original coefficient module for every left coset of `H` in `G`. -/
noncomputable abbrev restrictedCoinducedCoefficient
    (B : Rep k (⊥ : Subgroup G)) : Rep k (⊥ : Subgroup H) :=
  Rep.trivial k (⊥ : Subgroup H) ((G ⧸ H) → B)

/-- Restricting a representation coinduced from the trivial subgroup of `G`
to any subgroup `H` produces a representation coinduced from the trivial
subgroup of `H`.

The construction is coordinatewise on the decomposition `G ≃ (G / H) × H`;
no finiteness or normality hypothesis is involved. -/
noncomputable def restrictCoinducedBottom
    (B : Rep k (⊥ : Subgroup G)) :
    Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype B) ≅
      Rep.coind (⊥ : Subgroup H).subtype
        (restrictedCoinducedCoefficient H B) := by
  let e : Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype B) ≃ₗ[k]
      Rep.coind (⊥ : Subgroup H).subtype
        (restrictedCoinducedCoefficient H B) :=
    { toFun := fun f ↦
        ⟨fun h q ↦ f.1 ((unrestrictedRightCoset H).symm (q, h)), by
          intro b h
          have hb : b = (1 : (⊥ : Subgroup H)) :=
            Subtype.ext (Subgroup.mem_bot.mp b.2)
          subst hb
          simp⟩
      invFun := fun f ↦
        ⟨fun g ↦ f.1 (unrestrictedCosetCoordinate H g)
            (QuotientGroup.mk g : G ⧸ H), by
          intro b g
          have hb : b = (1 : (⊥ : Subgroup G)) :=
            Subtype.ext (Subgroup.mem_bot.mp b.2)
          subst hb
          simp⟩
      left_inv := fun f ↦ by
        apply Subtype.ext
        funext g
        exact congrArg f.1
          (unrestricted_coset_coordinate H g)
      right_inv := fun f ↦ by
        apply Subtype.ext
        funext h q
        change f.1
            (unrestrictedCosetCoordinate H (Quotient.out q * h))
            (QuotientGroup.mk (Quotient.out q * h) : G ⧸ H) = f.1 h q
        rw [unrestricted_coset_representative]
        simp [QuotientGroup.mk_mul_of_mem]
      map_add' := fun f g ↦ by
        apply Subtype.ext
        funext h q
        rfl
      map_smul' := fun r f ↦ by
        apply Subtype.ext
        funext h q
        rfl }
  exact Rep.mkIso {
    toLinearEquiv := e
    isIntertwining' := fun h ↦ by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext x q
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      dsimp only [e]
      apply congrArg f.1
      simp [unrestrictedRightCoset, mul_assoc] }

/-- Restriction to an arbitrary subgroup of a module coinduced from the
trivial subgroup has zero positive-degree cohomology. -/
theorem coinduced_bottom_acyclic
    (B : Rep k (⊥ : Subgroup G)) (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology
      (Rep.res H.subtype (Rep.coind (⊥ : Subgroup G).subtype B)) n) :=
  (zero_cohomology_coinduced
    (restrictedCoinducedCoefficient H B) n hn).of_iso
      ((groupCohomology.functor k H n).mapIso
        (restrictCoinducedBottom H B))

/-- In particular, the middle term of Milne's canonical dimension-shifting
sequence remains acyclic after restriction to an arbitrary subgroup. -/
theorem middle_unconditional_acyclic
    (A : Rep k G) (n : ℕ) (hn : 0 < n) :
    IsZero (groupCohomology
      (Rep.res H.subtype (dimensionShiftSequence A).X₂) n) := by
  change IsZero (groupCohomology
    (Rep.res H.subtype
      (Rep.coind (⊥ : Subgroup G).subtype
        (Rep.res (⊥ : Subgroup G).subtype A))) n)
  exact coinduced_bottom_acyclic H
    (Rep.res (⊥ : Subgroup G).subtype A) n hn

end RestrictedCoinduction

end

end Towers.CField.COps
