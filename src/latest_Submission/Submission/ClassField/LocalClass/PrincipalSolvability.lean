import Submission.NumberTheory.Locals.RamificationGroups

/-!
# Solvability from the principal ramification filtration

This packages the concrete tame and higher ramification characters into the
abstract solvability criterion used in Milne's proof of Lemma III.2.6.
-/

namespace Submission.CField.LClass

open Submission.NumberTheory.Milne
open scoped Pointwise

noncomputable section

variable {R B G A₀ : Type*}
  [CommRing R] [CommRing B] [IsDomain B] [Algebra R B]
  [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G R B]
  [FaithfulSMul G B] [IsNoetherianRing B] [IsLocalRing B]
  [CommGroup A₀]

/-- If a proper principal ideal gives the ramification filtration, the
residue action detects `G/G₀`, and its generator generates the ring,
then the acting finite group is solvable.  The tame and wild quotient
detectors are supplied by the concrete ramification characters. -/
theorem solvable_ramification_characters
    (Pi : B) (hPi : Pi ≠ 0)
    (hproper : Ideal.span ({Pi} : Set B) ≠ ⊤)
    (hgen : Algebra.adjoin R ({Pi} : Set B) = ⊤)
    (φ₀ : G →* A₀)
    (hker₀ : ∀ sigma : G, φ₀ sigma = 1 →
      sigma ∈ idealRamificationGroup (Ideal.span ({Pi} : Set B)) G 0) :
    IsSolvable G := by
  let P : Ideal B := Ideal.span ({Pi} : Set B)
  let C : ℕ → Type _
    | 0 => (B ⧸ P)ˣ
    | _ + 1 => Multiplicative (B ⧸ P)
  letI hC : ∀ i, CommGroup (C i) := fun i ↦ by
    cases i <;> simp only [C] <;> infer_instance
  let φ : ∀ i : ℕ, idealRamificationGroup P G i →* C i
    | 0 => principalRamificationRatio (G := G) Pi hPi
    | i + 1 => principalHigherRamification
        (G := G) Pi hPi (i + 1) (Nat.succ_pos i)
  apply solvable_abelian_detectors
    P hproper φ₀ hker₀ C φ
  intro i sigma hsigma
  cases i with
  | zero =>
      have hmem : sigma ∈
          (principalRamificationRatio (G := G) Pi hPi).ker :=
        MonoidHom.mem_ker.mpr hsigma
      rw [principal_ramification_ratio
        (A := R) (G := G) Pi hPi hgen] at hmem
      exact hmem
  | succ i =>
      have hmem : sigma ∈
          (principalHigherRamification
            (G := G) Pi hPi (i + 1) (Nat.succ_pos i)).ker :=
        MonoidHom.mem_ker.mpr hsigma
      rw [principal_higher_ramification
        (A := R) (G := G) Pi hPi (i + 1) (Nat.succ_pos i) hgen] at hmem
      exact hmem

end

end Submission.CField.LClass
