import Submission.ClassField.CrossedProducts.RelativeGroupMono

/-!
# Cofinal direct limits of relative Brauer groups

A monotone sequence of finite Galois subextensions of a separable closure gives
a directed system of relative Brauer groups.  If every absolute Brauer class
is split at some level of the sequence, its direct limit is the absolute
Brauer group.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open BGroups CProduca

variable (K : Type u) [Field K]
variable (L : ℕ → FiniteGaloisIntermediateField K (SeparableClosure K))

/-- The relative Brauer group at level `r` of a sequence of finite Galois
extensions. -/
abbrev brauerCofinalLevel (r : ℕ) := ↥(relativeBrauerGroup K (L r))

/-- Inclusion between relative Brauer groups in a monotone sequence. -/
def brauerCofinalInclusion (hL : Monotone L) (r s : ℕ) (hrs : r ≤ s) :
    brauerCofinalLevel K L r →* brauerCofinalLevel K L s :=
  relativeBrauerInclusion K (hL hrs)

@[simp]
theorem cofinal_inclusion_coe
    (hL : Monotone L) (r s : ℕ) (hrs : r ≤ s)
    (x : brauerCofinalLevel K L r) :
    ((brauerCofinalInclusion K L hL r s hrs x :
        brauerCofinalLevel K L s) : BrauerGroup K) = x :=
  rfl

/-- Relative Brauer groups along a monotone sequence form a directed system. -/
instance brauerDirectedSystem (hL : Monotone L) :
    DirectedSystem (brauerCofinalLevel K L)
      (fun {_ _} h => brauerCofinalInclusion K L hL _ _ h) where
  map_self := by
    intro r x
    rfl
  map_map := by
    intro r s t hrs hst x
    rfl

/-- The direct limit of relative Brauer groups along a monotone sequence. -/
abbrev brauerCofinalLimit (hL : Monotone L) :=
  DirectLimit (brauerCofinalLevel K L) (brauerCofinalInclusion K L hL)

/-- The canonical map from a cofinal relative-Brauer direct limit to the
absolute Brauer group. -/
def cofinalLimit (hL : Monotone L) :
    brauerCofinalLimit K L hL →* BrauerGroup K where
  toFun := DirectLimit.lift (brauerCofinalInclusion K L hL)
    (fun _ x => (x : BrauerGroup K))
    (fun _ _ _ _ => rfl)
  map_one' := by
    rw [DirectLimit.one_def 0, DirectLimit.lift_def]
    rfl
  map_mul' := by
    intro x y
    induction x, y using DirectLimit.induction₂ with
    | _ r x y =>
        rw [DirectLimit.mul_def, DirectLimit.lift_def,
          DirectLimit.lift_def, DirectLimit.lift_def]
        rfl

@[simp]
theorem cofinal_limit_mk
    (hL : Monotone L) (r : ℕ) (x : brauerCofinalLevel K L r) :
    cofinalLimit K L hL
        (⟦⟨r, x⟩⟧ : brauerCofinalLimit K L hL) = (x : BrauerGroup K) :=
  rfl

/-- The canonical map from a relative-Brauer direct limit is injective. -/
theorem cofinal_limit_injective (hL : Monotone L) :
    Function.Injective (cofinalLimit K L hL) := by
  exact DirectLimit.lift_injective
    (f := brauerCofinalInclusion K L hL)
    (ih := fun _ (x : brauerCofinalLevel K L _) => (x : BrauerGroup K))
    (compat := fun _ _ _ _ => rfl)
    (fun _ => Subtype.val_injective)

/-- Cofinality of the sequence makes the canonical map onto the absolute
Brauer group surjective. -/
theorem brauer_cofinal_limit
    (hL : Monotone L)
    (hcofinal : ∀ x : BrauerGroup K, ∃ r, x ∈ relativeBrauerGroup K (L r)) :
    Function.Surjective (cofinalLimit K L hL) := by
  intro x
  obtain ⟨r, hx⟩ := hcofinal x
  let y : brauerCofinalLevel K L r := ⟨x, hx⟩
  exact ⟨(⟦⟨r, y⟩⟧ : brauerCofinalLimit K L hL), rfl⟩

/-- A cofinal monotone sequence of finite Galois splitting fields has relative
Brauer direct limit canonically equivalent to the absolute Brauer group. -/
def brauerCofinalEquiv
    (hL : Monotone L)
    (hcofinal : ∀ x : BrauerGroup K, ∃ r, x ∈ relativeBrauerGroup K (L r)) :
    brauerCofinalLimit K L hL ≃* BrauerGroup K :=
  MulEquiv.ofBijective (cofinalLimit K L hL)
    ⟨cofinal_limit_injective K L hL,
      brauer_cofinal_limit K L hL hcofinal⟩

@[simp]
theorem brauer_cofinal_mk
    (hL : Monotone L)
    (hcofinal : ∀ x : BrauerGroup K, ∃ r, x ∈ relativeBrauerGroup K (L r))
    (r : ℕ) (x : brauerCofinalLevel K L r) :
    brauerCofinalEquiv K L hL hcofinal
        (⟦⟨r, x⟩⟧ : brauerCofinalLimit K L hL) = (x : BrauerGroup K) :=
  rfl

end

end Submission.CField.LBrauer
