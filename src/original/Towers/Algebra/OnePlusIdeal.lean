import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Group elements congruent to one modulo an ideal

This file formalizes Lemma 2.2 of Efrat--Chapman. The proof only needs a
left ideal, although the paper applies it to a two-sided ideal in a group
ring.
-/

namespace EChapma

variable {G A : Type*} [Group G] [Ring A]

/--
The subgroup of elements whose image under `ι` is congruent to one modulo
the ideal `I`.
-/
def plusIdealSubgroup (ι : G →* A) (I : Ideal A) : Subgroup G where
  carrier := {g | ι g - 1 ∈ I}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change ι (g * h) - 1 ∈ I
    rw [map_mul]
    have hmul : ι g * (ι h - 1) ∈ I := I.mul_mem_left _ hh
    have hadd := I.add_mem hmul hg
    rw [show ι g * ι h - 1 =
      ι g * (ι h - 1) + (ι g - 1) by noncomm_ring]
    exact hadd
  inv_mem' {g} hg := by
    have hinv : ι g⁻¹ * ι g = 1 := by
      rw [← map_mul]
      simp
    have hmul : -(ι g⁻¹) * (ι g - 1) ∈ I :=
      I.mul_mem_left _ hg
    change ι g⁻¹ - 1 ∈ I
    rw [show ι g⁻¹ - 1 = -(ι g⁻¹) * (ι g - 1) by
      rw [neg_mul, mul_sub, hinv, mul_one]
      noncomm_ring]
    exact hmul

@[simp]
theorem one_plus_subgroup
    (ι : G →* A) (I : Ideal A) (g : G) :
    g ∈ plusIdealSubgroup ι I ↔ ι g - 1 ∈ I :=
  Iff.rfl

instance plus_ideal_normal
    (ι : G →* A) (I : Ideal A) [I.IsTwoSided] :
    (plusIdealSubgroup ι I).Normal where
  conj_mem x hx g := by
    change ι (g * x * g⁻¹) - 1 ∈ I
    rw [map_mul, map_mul]
    have hleft : ι g * (ι x - 1) ∈ I :=
      I.mul_mem_left _ hx
    have hright : ι g * (ι x - 1) * ι g⁻¹ ∈ I :=
      I.mul_mem_right _ hleft
    have hinv : ι g * ι g⁻¹ = 1 := by
      rw [← map_mul]
      simp
    rw [show ι g * ι x * ι g⁻¹ - 1 =
      ι g * (ι x - 1) * ι g⁻¹ by noncomm_ring [hinv]]
    exact hright

end EChapma
