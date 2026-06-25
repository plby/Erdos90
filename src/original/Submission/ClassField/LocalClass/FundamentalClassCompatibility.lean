import Submission.ClassField.LocalBrauer.DivisionAlgebraInvariant

/-!
# Compatibility of local fundamental classes

This file formalizes the invariant-theoretic argument in Lemma III.2.7.
Once the restriction, corestriction, or inflation square for local invariants
is known, the corresponding formula for fundamental classes follows from the
identity `d * (1 / (d * m)) = 1 / m` in `Q/Z`.
-/

namespace Submission.CField.LClass

open LBrauer

/-- Multiplying `1 / (d * m)` by `d` gives `1 / m` in the local invariant
group. -/
theorem invariant_nsmul_div
    (d m : ℕ) [NeZero d] [NeZero m] :
    d • (((1 : ℚ) / ((d * m : ℕ) : ℚ) : LocalInvariant)) =
      ((1 : ℚ) / (m : ℚ) : LocalInvariant) := by
  rw [← AddCircle.coe_nsmul]
  apply congrArg (fun q : ℚ ↦ (q : LocalInvariant))
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hm : (m : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  change (d : ℚ) * (1 / ((d * m : ℕ) : ℚ)) = 1 / (m : ℚ)
  rw [Nat.cast_mul]
  field_simp

/-- Formula (31) of Lemma III.2.7.  If restriction multiplies the ambient
local invariant by `d`, it carries the fundamental class of degree `d * m`
to the fundamental class of degree `m`. -/
theorem restriction_fundamental_invariant
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (res : A →+ B) (invA : A →+ LocalInvariant)
    (invB : B →+ LocalInvariant) (uA : A) (uB : B)
    (d m : ℕ) [NeZero d] [NeZero m]
    (hinjB : Function.Injective invB)
    (huA : invA uA = ((1 : ℚ) / ((d * m : ℕ) : ℚ) : LocalInvariant))
    (huB : invB uB = ((1 : ℚ) / (m : ℚ) : LocalInvariant))
    (hres : ∀ x, invB (res x) = d • invA x) :
    res uA = uB := by
  apply hinjB
  rw [hres, huA, huB, invariant_nsmul_div]

/-- Formula (32) of Lemma III.2.7.  If corestriction preserves the ambient
local invariant, then the fundamental class in degree `m` corestricts to `d`
times the fundamental class in degree `d * m`. -/
theorem corestriction_fundamental_invariant
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (cor : B →+ A) (invA : A →+ LocalInvariant)
    (invB : B →+ LocalInvariant) (uA : A) (uB : B)
    (d m : ℕ) [NeZero d] [NeZero m]
    (hinjA : Function.Injective invA)
    (huA : invA uA = ((1 : ℚ) / ((d * m : ℕ) : ℚ) : LocalInvariant))
    (huB : invB uB = ((1 : ℚ) / (m : ℚ) : LocalInvariant))
    (hcor : ∀ x, invA (cor x) = invB x) :
    cor uB = d • uA := by
  apply hinjA
  rw [hcor, huB, map_nsmul, huA, invariant_nsmul_div]

/-- Formula (33) of Lemma III.2.7 has the same invariant-theoretic form as
the corestriction calculation: an invariant-preserving inflation sends the
smaller fundamental class to the relative-degree multiple of the larger
one. -/
theorem inflation_fundamental_invariant
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (inf : B →+ A) (invA : A →+ LocalInvariant)
    (invB : B →+ LocalInvariant) (uA : A) (uB : B)
    (d m : ℕ) [NeZero d] [NeZero m]
    (hinjA : Function.Injective invA)
    (huA : invA uA = ((1 : ℚ) / ((d * m : ℕ) : ℚ) : LocalInvariant))
    (huB : invB uB = ((1 : ℚ) / (m : ℚ) : LocalInvariant))
    (hinf : ∀ x, invA (inf x) = invB x) :
    inf uB = d • uA :=
  corestriction_fundamental_invariant
    inf invA invB uA uB d m hinjA huA huB hinf

end Submission.CField.LClass
