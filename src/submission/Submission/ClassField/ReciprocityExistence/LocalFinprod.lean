import Mathlib.Algebra.DirectSum.Module
import Submission.ClassField.Reciprocity.RestrictedFactorFamily

/-!
# Summing local character values

The right square in Lemma VII.8.5 is proved place by place.  This file
records the purely algebraic final step: the sum of those local character
values is the value of the same character on the finite product of local
Artin symbols.
-/

namespace Submission.CField.RExist

open Submission.CField.Recip
open scoped RestrictedProduct

noncomputable section

universe u v w z t

variable {ι : Type u} [DecidableEq ι]
variable {G : ι → Type v} [∀ i, CommGroup (G i)]
variable (U : ∀ i, Subgroup (G i))
variable {A : Type w} [CommGroup A]
variable {C : ι → Type z} [∀ i, AddCommGroup (C i)]
variable {B : Type t} [AddCommGroup B]

/-- The map out of a direct sum induced by a family of additive maps is the
finite sum of their values on the coordinates. -/
theorem direct_monoid_finsum
    (inv : ∀ i, C i →+ B) (b : DirectSum ι C) :
    DirectSum.toAddMonoid inv b = ∑ᶠ i, inv i (b i) := by
  classical
  change DFinsupp.sumAddHom inv b = _
  rw [DFinsupp.sumAddHom_apply]
  change (∑ i ∈ b.support, inv i (b i)) = ∑ᶠ i, inv i (b i)
  symm
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply (DFinsupp.mem_support_toFun b i).mpr
  intro hzero
  apply hi
  change inv i (b i) = 0
  rw [hzero, map_zero]

/-- The universal sum map on a direct sum of copies of an additive group is
the finite sum of its coordinates. -/
theorem direct_id_finsum
    (b : DirectSum ι (fun _ => B)) :
    DirectSum.toAddMonoid (fun _ => AddMonoidHom.id B) b =
      ∑ᶠ i, b i := by
  simpa using direct_monoid_finsum
    (C := fun _ => B) (fun _ => AddMonoidHom.id B) b

/-- If the `i`th coordinate is the value of `chi` on the `i`th local
factor, then the sum of the coordinates is `chi` evaluated on the restricted
finite product of all local factors. -/
theorem direct_character_restricted
    (D : RLFam (A := A) U)
    (chi : Additive A →+ B)
    (x : Πʳ i, [G i, U i])
    (inv : ∀ i, C i →+ B) (b : DirectSum ι C)
    (hb : ∀ i, inv i (b i) =
      chi (Additive.ofMul (D.localHom i (x i)))) :
    DirectSum.toAddMonoid inv b =
      chi (Additive.ofMul (D.restrictedProductHom U x)) := by
  classical
  rw [direct_monoid_finsum]
  rw [show (fun i => inv i (b i)) =
      (fun i => chi (Additive.ofMul (D.localHom i (x i)))) by
    funext i
    exact hb i]
  let chiMul : A →* Multiplicative B := chi.toMultiplicative
  have hfinite := D.finite_mulSupport U x
  have hmap := chiMul.map_finprod hfinite
  apply Multiplicative.ofAdd.injective
  change Multiplicative.ofAdd
      (∑ᶠ i, chi (Additive.ofMul (D.localHom i (x i)))) =
    Multiplicative.ofAdd
      (chi (Additive.ofMul (D.restrictedProductHom U x)))
  rw [finsum_eq_sum_of_support_subset
    (fun i => chi (Additive.ofMul (D.localHom i (x i))))]
  · change (∏ i ∈ hfinite.toFinset,
        chiMul (D.localHom i (x i))) =
      chiMul (∏ᶠ i, D.localHom i (x i))
    rw [hmap]
    exact (finprod_eq_prod_of_mulSupport_subset
      (fun i => chiMul (D.localHom i (x i))) (by
        intro i hi
        apply hfinite.mem_toFinset.2
        change D.localHom i (x i) ≠ 1
        intro hone
        apply hi
        change chiMul (D.localHom i (x i)) = 1
        rw [hone]
        exact map_one chiMul)).symm
  · intro i hi
    apply hfinite.mem_toFinset.2
    change D.localHom i (x i) ≠ 1
    intro hone
    apply hi
    change chi (Additive.ofMul (D.localHom i (x i))) = 0
    rw [hone]
    exact map_zero chi

end

end Submission.CField.RExist
