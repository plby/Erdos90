import Mathlib.Algebra.Module.CharacterModule
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The injective character used in Lemma VII.8.5

For a finite cyclic group `G`, Milne chooses an injective character
`G → Q/Z`.  This file constructs that character explicitly by identifying
the additive group with `ZMod |G|` and sending `j` to `j / |G|` modulo the
integers.
-/

namespace Submission.CField.RExist

noncomputable section

/-- The standard injective character `Z/nZ → Q/Z`. -/
noncomputable def zmodRationalCharacter (n : ℕ) [NeZero n] :
    ZMod n →+ AddCircle (1 : ℚ) :=
  ZMod.lift n
    ⟨AddMonoidHom.mk' (fun j : ℤ ↦ ((j / n : ℚ) : AddCircle (1 : ℚ)))
      (by intro x y; simp [add_div]),
      by
        have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
        simp [hn]⟩

@[simp]
theorem zmod_character_cast
    (n : ℕ) [NeZero n] (j : ℤ) :
    zmodRationalCharacter n (j : ZMod n) =
      ((j / n : ℚ) : AddCircle (1 : ℚ)) := by
  simp [zmodRationalCharacter]

@[simp]
theorem zmod_rational_cast
    (n : ℕ) [NeZero n] (j : ℕ) :
    zmodRationalCharacter n (j : ZMod n) =
      ((j / n : ℚ) : AddCircle (1 : ℚ)) := by
  simpa using zmod_character_cast n (j : ℤ)

theorem zmod_rational_character
    (n : ℕ) [NeZero n] (j : ZMod n) :
    zmodRationalCharacter n j =
      ((j.val / n : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← zmod_rational_cast n, ZMod.natCast_zmod_val]

theorem zmod_character_injective
    (n : ℕ) [NeZero n] :
    Function.Injective (zmodRationalCharacter n) := by
  intro x y hxy
  have hn : (0 : ℚ) < n := by exact_mod_cast NeZero.pos n
  rwa [zmod_rational_character, zmod_rational_character,
    AddCircle.coe_eq_coe_iff_of_mem_Ico,
    div_left_inj' hn.ne', Nat.cast_inj,
    (ZMod.val_injective n).eq_iff] at hxy <;>
    exact ⟨by positivity,
      by simpa only [zero_add, div_lt_one hn, Nat.cast_lt] using ZMod.val_lt _⟩

/-- The injective rational character normalized to send a specified cyclic
generator to `1 / |G|`. -/
noncomputable def generatorRationalCharacter
    (G : Type*) [AddCommGroup G] [Finite G]
    (g : G) (hg : ∀ x : G, x ∈ AddSubgroup.zmultiples g) :
    CharacterModule G := by
  letI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact (zmodRationalCharacter (Nat.card G)).comp
    (zmodAddEquivOfGenerator hg rfl).symm.toAddMonoidHom

theorem generator_character_injective
    (G : Type*) [AddCommGroup G] [Finite G]
    (g : G) (hg : ∀ x : G, x ∈ AddSubgroup.zmultiples g) :
    Function.Injective (generatorRationalCharacter G g hg) := by
  letI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact (zmod_character_injective (Nat.card G)).comp
    (zmodAddEquivOfGenerator hg rfl).symm.injective

@[simp]
theorem generator_rational_character
    (G : Type*) [AddCommGroup G] [Finite G]
    (g : G) (hg : ∀ x : G, x ∈ AddSubgroup.zmultiples g) :
    generatorRationalCharacter G g hg g =
      (((Nat.card G : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) := by
  letI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  change zmodRationalCharacter (Nat.card G)
      ((zmodAddEquivOfGenerator hg rfl).symm g) = _
  rw [zmodAddEquivOfGenerator_symm_apply_generator]
  simpa [one_div] using
    (zmod_character_cast (Nat.card G) (1 : ℤ))

/-- The same normalized character for a multiplicative cyclic group. -/
noncomputable def multiplicativeRationalCharacter
    (G : Type*) [CommGroup G] [Finite G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    CharacterModule (Additive G) :=
  generatorRationalCharacter (Additive G) (Additive.ofMul g) (by
    intro x
    change x.toMul ∈ Subgroup.zpowers g
    exact hg x.toMul)

theorem multiplicative_character_injective
    (G : Type*) [CommGroup G] [Finite G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    Function.Injective (multiplicativeRationalCharacter G g hg) :=
  generator_character_injective (Additive G) (Additive.ofMul g) (by
    intro x
    change x.toMul ∈ Subgroup.zpowers g
    exact hg x.toMul)

@[simp]
theorem multiplicative_rational_character
    (G : Type*) [CommGroup G] [Finite G]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    multiplicativeRationalCharacter G g hg (Additive.ofMul g) =
      (((Nat.card G : ℚ)⁻¹ : ℚ) : AddCircle (1 : ℚ)) :=
  generator_rational_character
    (Additive G) (Additive.ofMul g) (by
      intro x
      change x.toMul ∈ Subgroup.zpowers g
      exact hg x.toMul)

/-- A canonical-by-choice injective `Q/Z`-valued character on a finite
cyclic additive group. -/
noncomputable def cyclicRationalCharacter
    (G : Type*) [AddCommGroup G] [Finite G] [IsAddCyclic G] :
    CharacterModule G := by
  letI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact (zmodRationalCharacter (Nat.card G)).comp
    (zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic G)).symm.toAddMonoidHom

theorem cyclic_rational_character
    (G : Type*) [AddCommGroup G] [Finite G] [IsAddCyclic G] :
    Function.Injective (cyclicRationalCharacter G) := by
  letI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  exact (zmod_character_injective (Nat.card G)).comp
    (zmodAddCyclicAddEquiv
      (inferInstance : IsAddCyclic G)).symm.injective

end

end Submission.CField.RExist
