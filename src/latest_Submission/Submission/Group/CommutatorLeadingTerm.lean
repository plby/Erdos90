import Submission.Group.FreeAugmentationGraded
import Submission.Group.HallWords


open scoped commutatorElement

namespace Submission
namespace TBluepr

/-- Multiplication adds augmentation degrees in the historical augmentation
ideal API. -/
theorem golod_shafarevich_add
    (R G : Type*) [CommRing R] [Group G]
    {m n : ℕ}
    {a b : MonoidAlgebra R G}
    (ha : a ∈ (GShafar.augmentationIdeal R G) ^ m)
    (hb : b ∈ (GShafar.augmentationIdeal R G) ^ n) :
    a * b ∈ (GShafar.augmentationIdeal R G) ^ (m + n) := by
  rw [Ideal.IsTwoSided.pow_add]
  exact Ideal.mul_mem_mul ha hb

/--
The augmentation difference of a group commutator has leading term
`δ(g) * δ(h) - δ(h) * δ(g)`.  The remaining terms have one extra
augmentation degree.
-/
theorem difference_sub_leading
    (R G : Type*) [CommRing R] [Group G]
    {m n : ℕ}
    {g h : G}
    (hg :
      augmentationDifference R G g ∈
        (GShafar.augmentationIdeal R G) ^ m)
    (hh :
      augmentationDifference R G h ∈
        (GShafar.augmentationIdeal R G) ^ n) :
    augmentationDifference R G (g * h * g⁻¹ * h⁻¹) -
        (augmentationDifference R G g * augmentationDifference R G h -
          augmentationDifference R G h * augmentationDifference R G g) ∈
      (GShafar.augmentationIdeal R G) ^ (m + n + 1) := by
  let I := GShafar.augmentationIdeal R G
  let c :=
    augmentationDifference R G g * augmentationDifference R G h -
      augmentationDifference R G h * augmentationDifference R G g
  have hgh :
      augmentationDifference R G g * augmentationDifference R G h ∈
        I ^ (m + n) :=
    golod_shafarevich_add R G hg hh
  have hhg :
      augmentationDifference R G h * augmentationDifference R G g ∈
        I ^ (m + n) := by
    simpa [Nat.add_comm] using
      golod_shafarevich_add R G hh hg
  have hc : c ∈ I ^ (m + n) :=
    sub_mem hgh hhg
  have hinv :
      augmentationDifference R G (g⁻¹ * h⁻¹) ∈ I ^ 1 := by
    simpa [I, Submodule.pow_one] using
      augmentation_difference_ideal R G (g⁻¹ * h⁻¹)
  have hprod :
      c * augmentationDifference R G (g⁻¹ * h⁻¹) ∈
        I ^ (m + n + 1) := by
    simpa [Nat.add_assoc] using
      golod_shafarevich_add R G hc hinv
  change
    (MonoidAlgebra.of R G (g * h * g⁻¹ * h⁻¹) - 1) -
        ((MonoidAlgebra.of R G g - 1) * (MonoidAlgebra.of R G h - 1) -
          (MonoidAlgebra.of R G h - 1) * (MonoidAlgebra.of R G g - 1)) ∈
      I ^ (m + n + 1)
  rw [GShafar.commutator_sub_one]
  simpa [I, c, augmentationDifference, mul_sub, mul_assoc] using hprod

/--
Changing both inputs of an associative commutator by one-higher filtration
terms changes the commutator by one-higher total filtration degree.
-/
theorem associative_sub_succ
    (R G : Type*) [CommRing R] [Group G]
    {m n : ℕ}
    {u u' v v' : MonoidAlgebra R G}
    (hu : u ∈ (GShafar.augmentationIdeal R G) ^ m)
    (hu' : u' ∈ (GShafar.augmentationIdeal R G) ^ m)
    (hv : v ∈ (GShafar.augmentationIdeal R G) ^ n)
    (hv' : v' ∈ (GShafar.augmentationIdeal R G) ^ n)
    (hdu : u - u' ∈ (GShafar.augmentationIdeal R G) ^ (m + 1))
    (hdv : v - v' ∈ (GShafar.augmentationIdeal R G) ^ (n + 1)) :
    (u * v - v * u) - (u' * v' - v' * u') ∈
      (GShafar.augmentationIdeal R G) ^ (m + n + 1) := by
  let I := GShafar.augmentationIdeal R G
  have hleftOne : (u - u') * v ∈ I ^ (m + n + 1) := by
    simpa [I, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      golod_shafarevich_add R G hdu hv
  have hleftTwo : u' * (v - v') ∈ I ^ (m + n + 1) := by
    simpa [I, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      golod_shafarevich_add R G hu' hdv
  have hrightOne : (v - v') * u ∈ I ^ (m + n + 1) := by
    simpa [I, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      golod_shafarevich_add R G hdv hu
  have hrightTwo : v' * (u - u') ∈ I ^ (m + n + 1) := by
    simpa [I, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      golod_shafarevich_add R G hv' hdu
  have hsum :
      ((u - u') * v + u' * (v - v')) -
          ((v - v') * u + v' * (u - u')) ∈
        I ^ (m + n + 1) :=
    sub_mem (add_mem hleftOne hleftTwo) (add_mem hrightOne hrightTwo)
  convert hsum using 1 ; noncomm_ring

/--
The noncommutative leading polynomial associated to a binary commutator word
in free generators.
-/
noncomputable def freeLeadingPolynomial
    (R α : Type*) [CommRing R] :
    CWord α → MonoidAlgebra R (FreeGroup α)
  | .atom a =>
      augmentationDifference R (FreeGroup α) (FreeGroup.of a)
  | .commutator u v =>
      freeLeadingPolynomial R α u *
          freeLeadingPolynomial R α v -
        freeLeadingPolynomial R α v *
          freeLeadingPolynomial R α u

/-- The leading polynomial of a commutator word has its expected augmentation
degree. -/
theorem free_leading_pow
    (R α : Type*) [CommRing R] :
    ∀ w : CWord α,
      freeLeadingPolynomial R α w ∈
        (GShafar.augmentationIdeal R (FreeGroup α)) ^
          (w.weight fun _ => 1)
  | .atom a => by
      simpa [freeLeadingPolynomial, Submodule.pow_one] using
        augmentation_difference_ideal
          R (FreeGroup α) (FreeGroup.of a)
  | .commutator u v => by
      have huv :=
        golod_shafarevich_add
          R (FreeGroup α)
          (free_leading_pow R α u)
          (free_leading_pow R α v)
      have hvu :=
        golod_shafarevich_add
          R (FreeGroup α)
          (free_leading_pow R α v)
          (free_leading_pow R α u)
      exact sub_mem huv (by simpa [Nat.add_comm] using hvu)

/-- Evaluating a commutator word in free generators has the expected
augmentation degree. -/
theorem free_commutator_difference
    (R α : Type*) [CommRing R] :
    ∀ w : CWord α,
      augmentationDifference R (FreeGroup α) (w.eval FreeGroup.of) ∈
        (GShafar.augmentationIdeal R (FreeGroup α)) ^
          (w.weight fun _ => 1)
  | .atom a => by
      simpa [Submodule.pow_one] using
        augmentation_difference_ideal
          R (FreeGroup α) (FreeGroup.of a)
  | .commutator u v => by
      have hcomm :=
        GShafar.commutator_augmentation_subgroup
          (R := R) (G := FreeGroup α)
          (free_commutator_difference R α u)
          (free_commutator_difference R α v)
      simpa [GShafar.augmentationPowerSubgroup,
        augmentationDifference, commutatorElement_def] using hcomm

/--
The augmentation difference of an evaluated binary commutator word agrees
with its recursively defined noncommutative leading polynomial modulo the
next augmentation power.
-/
theorem difference_leading_succ
    (R α : Type*) [CommRing R] :
    ∀ w : CWord α,
      augmentationDifference R (FreeGroup α) (w.eval FreeGroup.of) -
          freeLeadingPolynomial R α w ∈
        (GShafar.augmentationIdeal R (FreeGroup α)) ^
          ((w.weight fun _ => 1) + 1)
  | .atom a => by
      simp [freeLeadingPolynomial]
  | .commutator u v => by
      let du :=
        augmentationDifference R (FreeGroup α) (u.eval FreeGroup.of)
      let dv :=
        augmentationDifference R (FreeGroup α) (v.eval FreeGroup.of)
      let pu := freeLeadingPolynomial R α u
      let pv := freeLeadingPolynomial R α v
      have hcomm :
          augmentationDifference R (FreeGroup α)
                (u.eval FreeGroup.of * v.eval FreeGroup.of *
                  (u.eval FreeGroup.of)⁻¹ * (v.eval FreeGroup.of)⁻¹) -
              (du * dv - dv * du) ∈
            (GShafar.augmentationIdeal R (FreeGroup α)) ^
              (u.weight (fun _ => 1) + v.weight (fun _ => 1) + 1) := by
        exact
          difference_sub_leading
            R (FreeGroup α)
            (free_commutator_difference R α u)
            (free_commutator_difference R α v)
      have hreplace :
          (du * dv - dv * du) - (pu * pv - pv * pu) ∈
            (GShafar.augmentationIdeal R (FreeGroup α)) ^
              (u.weight (fun _ => 1) + v.weight (fun _ => 1) + 1) := by
        exact
          associative_sub_succ
            R (FreeGroup α)
            (free_commutator_difference R α u)
            (free_leading_pow R α u)
            (free_commutator_difference R α v)
            (free_leading_pow R α v)
            (difference_leading_succ
              R α u)
            (difference_leading_succ
              R α v)
      have hadd :=
        add_mem hcomm hreplace
      simpa [CWord.eval, freeLeadingPolynomial,
        commutatorElement_def, du, dv, pu, pv] using hadd

/-- The leading polynomial of a binary commutator word, represented in its
expected augmentation power. -/
noncomputable def freeLeadingRep
    (R α : Type*) [CommRing R]
    (w : CWord α) :
    GroupAlgebra.augmentationPowerSubmodule R (FreeGroup α)
      (w.weight fun _ => 1) := by
  refine ⟨freeLeadingPolynomial R α w, ?_⟩
  simpa [GroupAlgebra.augmentationPower,
    ← golod_shafarevich_algebra] using
      free_leading_pow R α w

/-- The associated-graded class of the leading polynomial of a binary
commutator word. -/
noncomputable def freeLeadingLayer
    (R α : Type*) [CommRing R]
    (w : CWord α) :
    GroupAlgebra.augmentationLayer R (FreeGroup α)
      (w.weight fun _ => 1) :=
  Submodule.Quotient.mk (freeLeadingRep R α w)

/-- The evaluated binary commutator word, represented by its augmentation
difference in the expected augmentation power. -/
noncomputable def freeDifferenceRep
    (R α : Type*) [CommRing R]
    (w : CWord α) :
    GroupAlgebra.augmentationPowerSubmodule R (FreeGroup α)
      (w.weight fun _ => 1) := by
  refine
    ⟨augmentationDifference R (FreeGroup α) (w.eval FreeGroup.of), ?_⟩
  simpa [GroupAlgebra.augmentationPower,
    ← golod_shafarevich_algebra] using
      free_commutator_difference R α w

/-- The augmentation-layer class represented by an evaluated binary
commutator word. -/
noncomputable def freeDifferenceLayer
    (R α : Type*) [CommRing R]
    (w : CWord α) :
    GroupAlgebra.augmentationLayer R (FreeGroup α)
      (w.weight fun _ => 1) :=
  Submodule.Quotient.mk (freeDifferenceRep R α w)

/--
In the associated graded augmentation algebra, an evaluated binary commutator
word is represented exactly by its recursively defined noncommutative leading
polynomial.
-/
theorem free_difference_leading
    (R α : Type*) [CommRing R]
    (w : CWord α) :
    freeDifferenceLayer R α w =
      freeLeadingLayer R α w := by
  apply
    (Submodule.Quotient.eq
      (GroupAlgebra.augmentationLayerDenom R (FreeGroup α)
        (w.weight fun _ => 1))).mpr
  change
    augmentationDifference R (FreeGroup α) (w.eval FreeGroup.of) -
        freeLeadingPolynomial R α w ∈
      GroupAlgebra.augmentationPower R (FreeGroup α)
        ((w.weight fun _ => 1) + 1)
  simpa [GroupAlgebra.augmentationPower,
    ← golod_shafarevich_algebra] using
      difference_leading_succ
        R α w

end TBluepr
end Submission
