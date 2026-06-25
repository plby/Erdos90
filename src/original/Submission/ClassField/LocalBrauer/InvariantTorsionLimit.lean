import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Data.Nat.Factorial.Basic
import Submission.ClassField.LocalBrauer.LocalInvariantTorsion

/-!
# Chapter IV, Section 4: the local invariant as a torsion direct limit

The factorial degrees `(r + 2)!` form a cofinal divisibility sequence.  The
direct limit of the corresponding finite torsion subgroups of `ℚ/ℤ` is
therefore the whole local invariant group.  This is the target-side direct
limit used in Proposition IV.4.3.
-/

namespace Submission.CField.LBrauer

noncomputable section

/-- A cofinal sequence of degrees, all strictly greater than one. -/
def invariantLevelDegree (r : ℕ) : ℕ := Nat.factorial (r + 2)

theorem invariant_level_pos (r : ℕ) :
    0 < invariantLevelDegree r := by
  exact Nat.factorial_pos _

theorem invariant_level_dvd {r s : ℕ} (h : r ≤ s) :
    invariantLevelDegree r ∣ invariantLevelDegree s := by
  apply Nat.factorial_dvd_factorial
  omega

/-- Inclusion between factorial torsion levels. -/
def localTorsionInclusion (r s : ℕ) (h : r ≤ s) :
    localInvariantTorsion (invariantLevelDegree r) →+
      localInvariantTorsion (invariantLevelDegree s) :=
  AddSubgroup.inclusion <| by
    intro x hx
    change invariantLevelDegree s • (x : LocalInvariant) = 0
    have hx' : invariantLevelDegree r • (x : LocalInvariant) = 0 := hx
    obtain ⟨c, hc⟩ := invariant_level_dvd h
    rw [hc, mul_nsmul, hx', nsmul_zero]

@[simp]
theorem torsion_inclusion_coe
    (r s : ℕ) (h : r ≤ s)
    (x : localInvariantTorsion (invariantLevelDegree r)) :
    ((localTorsionInclusion r s h x :
        localInvariantTorsion (invariantLevelDegree s)) : LocalInvariant) = x :=
  rfl

instance invariantDirectedSystem :
    DirectedSystem
      (fun r : ℕ ↦ localInvariantTorsion (invariantLevelDegree r))
      (fun {_ _} h ↦ localTorsionInclusion _ _ h) where
  map_self := by
    intro r x
    rfl
  map_map := by
    intro r s t hrs hst x
    rfl

/-- Direct limit of the factorial torsion levels. -/
abbrev torsionLimit :=
  DirectLimit
    (fun r : ℕ ↦ localInvariantTorsion (invariantLevelDegree r))
    localTorsionInclusion

/-- Evaluation of a factorial torsion class in `ℚ/ℤ`. -/
noncomputable def invariantTorsionLimit :
    torsionLimit →+ LocalInvariant where
  toFun := DirectLimit.lift localTorsionInclusion
    (fun _ x ↦ (x : LocalInvariant))
    (fun _ _ _ _ ↦ rfl)
  map_zero' := by
    rw [DirectLimit.zero_def 0, DirectLimit.lift_def]
    rfl
  map_add' x y := by
    induction x, y using DirectLimit.induction₂ with
    | _ r x y =>
        rw [DirectLimit.add_def, DirectLimit.lift_def,
          DirectLimit.lift_def, DirectLimit.lift_def]
        rfl

theorem torsion_limit_injective :
    Function.Injective invariantTorsionLimit := by
  exact DirectLimit.lift_injective
    (f := localTorsionInclusion)
    (ih := fun r (x : localInvariantTorsion (invariantLevelDegree r)) ↦
      (x : LocalInvariant))
    (compat := fun _ _ _ _ ↦ rfl)
    (fun _ ↦ Subtype.val_injective)

theorem torsion_limit_surjective :
    Function.Surjective invariantTorsionLimit := by
  intro x
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  let r := q.den
  have hden : q.den • (q : LocalInvariant) = 0 := by
    have horder : addOrderOf (q : LocalInvariant) = q.den := by
      simpa using (AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := q))
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero (q : LocalInvariant)
  have hdvd : q.den ∣ invariantLevelDegree r := by
    apply Nat.dvd_factorial q.pos
    simp [r]
  have hlevel : invariantLevelDegree r • (q : LocalInvariant) = 0 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, mul_nsmul, hden, nsmul_zero]
  let y : localInvariantTorsion (invariantLevelDegree r) := ⟨q, hlevel⟩
  refine ⟨(⟦⟨r, y⟩⟧ : torsionLimit), ?_⟩
  rfl

/-- The factorial torsion direct limit is canonically `ℚ/ℤ`. -/
noncomputable def localTorsionLimit :
    torsionLimit ≃+ LocalInvariant :=
  AddEquiv.ofBijective invariantTorsionLimit
    ⟨torsion_limit_injective,
      torsion_limit_surjective⟩

end

end Submission.CField.LBrauer
