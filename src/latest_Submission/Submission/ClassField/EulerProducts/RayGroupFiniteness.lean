import Submission.ClassField.EulerProducts.IntegralIdealsNorm
import Submission.ClassField.EulerProducts.PartialZeta
import Submission.ClassField.RayClassGroups.GroupFiniteness

/-!
# Chapter VI, Section 2, Corollary 2.11

For a complex character of a ray class group, its Hecke `L`-function is the
finite character-weighted sum of the partial zeta functions of the ray
classes.  Corollary 2.9 gives every summand the same polar part.  Lemma 2.10
then kills that common part for a nontrivial character, leaving a holomorphic
function on the full half-plane `Re(s) > 1 - 1 / d`.
-/

namespace Submission.CField.EProduc

open Complex Finset Ideal IsDedekindDomain NumberField Set
open Submission.CField.RCGroups

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- The algebraic finiteness assertion implicit in the phrase "ray class
group".  It is discharged below by the finite residue-and-sign encoding. -/
def RayClassFiniteness : Prop :=
  ∀ m : Modulus K, Finite (RayClassGroup K m)

/-- Ray-class finiteness, supplied by the finite residue-and-sign encoding. -/
theorem rayClassFiniteness : RayClassFiniteness K :=
  ray_class_group K

/-- The ray-class `L`-series, on its initial half-plane, written exactly as
the finite sum `L(s,chi) = sum_k chi(k) zeta(s,k)` from the source. -/
def lPartialZeta (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ) : ℂ → ℂ :=
  fun s ↦ ∑ᶠ k, (chi k : ℂ) * rayPartialZeta K m k s

/-- The continuation obtained by replacing every partial zeta function by
the continuation of Corollary 2.9. -/
def rayLContinuation (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ) : ℂ → ℂ :=
  fun s ↦ ∑ᶠ k, (chi k : ℂ) * partialZetaContinuation K m k s

/-- After cancellation of the common pole, this is the holomorphic part of
the nontrivial ray-class `L`-function. -/
def lHolomorphicPart (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ) : ℂ → ℂ :=
  fun s ↦ ∑ᶠ k, (chi k : ℂ) * partialHolomorphicPart K m k s

/-- Literal conclusion of Corollary VI.2.11: the continuation agrees with
the defining ray-class `L`-series for `Re(s)>1` and is analytic throughout
`Re(s)>1-1/d`. -/
def RayFinitenessConclusion (m : Modulus K)
    (chi : RayClassGroup K m →* ℂˣ) : Prop :=
  (∀ s : ℂ, 1 < s.re →
    rayLContinuation K m chi s = lPartialZeta K m chi s) ∧
  DifferentiableOn ℂ (rayLContinuation K m chi)
    {s : ℂ | 1 - 1 / (numberFieldDegree K : ℝ) < s.re}

/-- Corollary 2.9 and character orthogonality imply Corollary 2.11, without
any additional hypothesis on the character or modulus. -/
theorem rayFinitenessStatement
    (hfinite : RayClassFiniteness K)
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k)) :
    (∀ (m : Modulus K) (chi : RayClassGroup K m →* ℂˣ), chi ≠ 1 →
          RayFinitenessConclusion K m chi) := by
  intro m chi hchi
  letI : Finite (RayClassGroup K m) := hfinite m
  letI : Fintype (RayClassGroup K m) := Fintype.ofFinite _
  let U : Set ℂ := {s : ℂ | 1 - 1 / (numberFieldDegree K : ℝ) < s.re}
  have hsum : ∑ k, (chi k : ℂ) = 0 :=
    Submission.CField.EProduc.character_sum_zero
      (A := RayClassGroup K m) chi hchi
  have hparts : ∀ k : RayClassGroup K m,
      DifferentiableOn ℂ (partialHolomorphicPart K m k) U := by
    intro k
    exact (h29 m k).2.2.2.1
  have hhol : DifferentiableOn ℂ (lHolomorphicPart K m chi) U := by
    intro s hs
    have heq : lHolomorphicPart K m chi =
        fun z ↦ ∑ k : RayClassGroup K m,
          (chi k : ℂ) * partialHolomorphicPart K m k z := by
      funext z
      simp [lHolomorphicPart, finsum_eq_sum_of_fintype]
    rw [heq]
    exact DifferentiableWithinAt.fun_sum fun k hk ↦
      (hparts k s hs).const_mul (chi k : ℂ)
  have heq : ∀ s : ℂ,
      rayLContinuation K m chi s = lHolomorphicPart K m chi s := by
    intro s
    simp only [rayLContinuation, lHolomorphicPart,
      finsum_eq_sum_of_fintype]
    calc
      ∑ k, (chi k : ℂ) * partialZetaContinuation K m k s =
          ∑ k, (chi k : ℂ) *
            ((rayCountingConstant K m : ℂ) / (s - 1) +
              partialHolomorphicPart K m k s) := by
        apply sum_congr rfl
        intro k hk
        rw [(h29 m k).2.2.2.2.1 s]
      _ = ((rayCountingConstant K m : ℂ) / (s - 1)) *
            ∑ k, (chi k : ℂ) +
          ∑ k, (chi k : ℂ) * partialHolomorphicPart K m k s := by
        simp_rw [mul_add]
        rw [sum_add_distrib, mul_comm, ← sum_mul]
      _ = ∑ k, (chi k : ℂ) * partialHolomorphicPart K m k s := by
        rw [hsum, mul_zero, zero_add]
  constructor
  · intro s hs
    simp only [rayLContinuation, lPartialZeta,
      finsum_eq_sum_of_fintype]
    apply sum_congr rfl
    intro k hk
    rw [(h29 m k).1 s hs]
  · intro s hs
    rw [show rayLContinuation K m chi = lHolomorphicPart K m chi from
      funext heq]
    exact hhol s hs

/-- Corollary 2.11 with its ray-class finiteness input discharged. -/
theorem ray_finiteness_counts
    (h29 : (∀ (m : Modulus K) (k : RayClassGroup K m), RayIdealsConclusion K m k)) :
    (∀ (m : Modulus K) (chi : RayClassGroup K m →* ℂˣ), chi ≠ 1 →
          RayFinitenessConclusion K m chi) :=
  rayFinitenessStatement K
    (rayClassFiniteness K) h29

end

end Submission.CField.EProduc
