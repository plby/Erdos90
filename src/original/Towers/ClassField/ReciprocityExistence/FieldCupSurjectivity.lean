import Towers.ClassField.ReciprocityExistence.GlobalFieldCup
import Towers.ClassField.ReciprocityExistence.CyclicTransport

/-!
# Surjectivity of the field-side cup product for cyclic extensions

For a finite cyclic Galois extension, every invariant unit of the extension
comes from the base field.  Combining this with cyclic cup-product
surjectivity proves that the literal field cup in Lemma VII.8.5 is onto the
relative Brauer group.
-/

namespace Towers.CField.RExist

open Towers.CField.LRecip
open Towers.CField.BLoc

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- Every Galois-invariant unit of `L` is the image of a unit of `K`. -/
theorem global_base_surjective :
    Function.Surjective (globalUnitInvariant K L) := by
  intro x
  let u : Additive Lˣ := x.1
  have hfixed : ∀ sigma : Gal(L/K),
      sigma ((u.toMul : Lˣ) : L) = ((u.toMul : Lˣ) : L) := by
    intro sigma
    have hx := x.2 sigma
    change Additive.ofMul (Units.map sigma u.toMul) = u at hx
    exact congrArg (fun u : Additive Lˣ ↦ ((u.toMul : Lˣ) : L))
      hx
  obtain ⟨a, ha⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed
      (F := K) (E := L) ((u.toMul : Lˣ) : L)).2 hfixed
  have ha0 : a ≠ 0 := by
    intro ha0
    rw [ha0, map_zero] at ha
    exact u.toMul.ne_zero ha.symm
  refine ⟨Units.mk0 a ha0, ?_⟩
  apply Subtype.ext
  change Additive.ofMul (Units.map (algebraMap K L) (Units.mk0 a ha0)) = u
  apply Additive.toMul.injective
  apply Units.ext
  exact ha

/-- Before identifying `H²` with the relative Brauer group, the literal
field cup by the transported normalized character is surjective. -/
theorem global_boundary_surjective
    (n : ℕ) [NeZero n]
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) :
    Function.Surjective (fun a : Additive Kˣ ↦
      globalCharacterBoundary K L a.toMul
        (transportedStandardCharacter n Gal(L/K) e)) := by
  intro z
  obtain ⟨pi, hpi⟩ := transported_boundary_surjective
    n Gal(L/K) Lˣ e z
  obtain ⟨a, ha⟩ := global_base_surjective K L pi
  refine ⟨Additive.ofMul a, ?_⟩
  change transportedCyclicBoundary n Gal(L/K) Lˣ e
      (globalUnitInvariant K L a) = z
  rw [ha]
  exact hpi

/-- The actual field-side map into the relative Brauer group is surjective
for the transported normalized cyclic character. -/
theorem global_transported_surjective
    (n : ℕ) [NeZero n]
    (e : Multiplicative (ZMod n) ≃* Gal(L/K)) :
    Function.Surjective
      (globalFieldCup K L
        (transportedStandardCharacter n Gal(L/K) e)) := by
  intro beta
  obtain ⟨a, ha⟩ := global_boundary_surjective
    K L n e (relativeBrauerCohomology K L beta)
  refine ⟨a, ?_⟩
  apply (relativeBrauerCohomology K L).injective
  rw [global_field_cup]
  exact ha

/-- A finite cyclic Galois extension admits an injective character whose
literal field cup is surjective. -/
theorem injective_cup_surjective
    [IsCyclic Gal(L/K)] :
    ∃ chi : RationalCharacter Gal(L/K),
      Function.Injective chi ∧ Function.Surjective (globalFieldCup K L chi) := by
  let n := Nat.card Gal(L/K)
  letI : NeZero n := ⟨Nat.card_pos.ne'⟩
  let e : Multiplicative (ZMod n) ≃* Gal(L/K) :=
    zmodCyclicMulEquiv (inferInstance : IsCyclic Gal(L/K))
  exact ⟨transportedStandardCharacter n Gal(L/K) e,
    transported_standard_injective n Gal(L/K) e,
    global_transported_surjective K L n e⟩

end

end Towers.CField.RExist
