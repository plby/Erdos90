import Submission.ClassField.LocalBrauer.CanonicalCarryInflation
import Submission.ClassField.CrossedProducts.CohomologyRestriction

/-!
# Restriction of cyclic carry cocycles

The subgroup of order `m` in a cyclic group of order `m * f` sends the
standard generator to the `f`-th power of the ambient generator.  On cyclic
indices this is multiplication by `f`, and it preserves Milne's carry bit.
-/

namespace Submission.CField.LBrauer.CCarry

noncomputable section

open CProduca

/-- The additive embedding `Z/m → Z/(m*f)` given by multiplication by
`f`. -/
def subgroupAddHom (m f : ℕ) : ZMod m →+ ZMod (m * f) :=
  ZMod.lift m
    ⟨(AddMonoidHom.mulLeft (f : ZMod (m * f))).comp
        (Int.castAddHom (ZMod (m * f))), by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft]
      have hm : (Int.castAddHom (ZMod (m * f))) (m : ℤ) =
          (m : ZMod (m * f)) := by
        simpa only [Int.coe_castAddHom] using
          (Int.cast_natCast m : ((m : ℤ) : ZMod (m * f)) = (m : ZMod (m * f)))
      rw [hm]
      calc
        (f : ZMod (m * f)) * (m : ZMod (m * f)) =
            ((f * m : ℕ) : ZMod (m * f)) := (Nat.cast_mul f m).symm
        _ = ((m * f : ℕ) : ZMod (m * f)) := by rw [Nat.mul_comm]
        _ = 0 := ZMod.natCast_self (m * f)⟩

/-- The corresponding embedding between multiplicative copies of the cyclic
groups. -/
def subgroupHom (m f : ℕ) :
    Multiplicative (ZMod m) →* Multiplicative (ZMod (m * f)) :=
  (subgroupAddHom m f).toMultiplicative

@[simp]
theorem subgroup_nat_cast (m f a : ℕ) :
    subgroupAddHom m f (a : ZMod m) = (a * f : ℕ) := by
  change ZMod.lift m _ (a : ZMod m) = _
  rw [show (a : ZMod m) = (a : ℤ) by norm_num, ZMod.lift_coe]
  simp [Nat.cast_mul, mul_comm]

@[simp]
theorem subgroup_hom_add (m f : ℕ) (a : Multiplicative (ZMod m)) :
    (subgroupHom m f a).toAdd = subgroupAddHom m f a.toAdd :=
  rfl

theorem subgroup_add_val {m f : ℕ} [NeZero m] [NeZero f]
    (a : ZMod m) :
    (subgroupAddHom m f a).val = a.val * f := by
  calc
    (subgroupAddHom m f a).val =
        (subgroupAddHom m f (a.val : ZMod m)).val := by
          rw [ZMod.natCast_zmod_val]
    _ = ((a.val * f : ℕ) : ZMod (m * f)).val := by
      rw [subgroup_nat_cast]
    _ = a.val * f := ZMod.val_natCast_of_lt
      (Nat.mul_lt_mul_of_pos_right (ZMod.val_lt a) (NeZero.pos f))

theorem subgroup_add_injective {m f : ℕ} [NeZero m] [NeZero f] :
    Function.Injective (subgroupAddHom m f) := by
  intro a b hab
  apply ZMod.val_injective
  apply Nat.eq_of_mul_eq_mul_right (NeZero.pos f)
  rw [← subgroup_add_val (f := f) a,
    ← subgroup_add_val (f := f) b, hab]

theorem subgroupHom_injective {m f : ℕ} [NeZero m] [NeZero f] :
    Function.Injective (subgroupHom m f) := by
  intro a b hab
  change a.toAdd = b.toAdd
  apply subgroup_add_injective (m := m) (f := f)
  exact congrArg Multiplicative.toAdd hab

/-- A homomorphism between cyclic groups is compatible with the standard
subgroup coordinates as soon as it is compatible on the standard
generator. -/
theorem subgroup_compatible_generator
    {m f : ℕ} [NeZero m] [NeZero f]
    {G H : Type*} [Group G] [Group H]
    (incl : H →* G)
    (eG : Multiplicative (ZMod (m * f)) ≃* G)
    (eH : Multiplicative (ZMod m) ≃* H)
    (hgen : incl (eH (CyclicH2.generator (n := m))) =
      eG (subgroupHom m f (CyclicH2.generator (n := m))))
    (z : Multiplicative (ZMod m)) :
    incl (eH z) = eG (subgroupHom m f z) := by
  rw [CyclicH2.generator_pow_val z, map_pow, map_pow, map_pow,
    hgen]
  exact (map_pow eG _ _).symm

/-- Multiplication by the subgroup index preserves the carry bit. -/
theorem carry_add_hom {m f : ℕ} [NeZero m] [NeZero f]
    (a b : ZMod m) :
    carry (subgroupAddHom m f a) (subgroupAddHom m f b) = carry a b := by
  rw [carry, carry, subgroup_add_val, subgroup_add_val]
  by_cases h : m ≤ a.val + b.val
  · simp only [if_pos h]
    rw [if_pos]
    simpa [Nat.add_mul] using Nat.mul_le_mul_right f h
  · have hlt : a.val + b.val < m := Nat.lt_of_not_ge h
    simp only [if_neg h]
    rw [if_neg]
    simpa [Nat.add_mul] using
      (Nat.mul_lt_mul_of_pos_right hlt (NeZero.pos f))

/-- Restricting the standard carry factor set on a cyclic group of order
`m * f` to its subgroup of order `m` gives the standard carry factor set on
that subgroup. -/
theorem restrict_set_subgroup {m f : ℕ} [NeZero m] [NeZero f]
    {M : Type*} [CommGroup M]
    [MulDistribMulAction (Multiplicative (ZMod (m * f))) M]
    [MulDistribMulAction (Multiplicative (ZMod m)) M]
    (hsmul : ∀ g : Multiplicative (ZMod m), ∀ x : M,
      g • x = subgroupHom m f g • x)
    (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod (m * f)), g • pi = pi) :
    NMCocycl₂.restrict (subgroupHom m f) hsmul
        (factorSet pi hpi) =
      factorSet pi (fun g ↦ (hsmul g pi).trans (hpi (subgroupHom m f g))) := by
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change pi ^ carry (subgroupAddHom m f g.toAdd)
      (subgroupAddHom m f h.toAdd) = pi ^ carry g.toAdd h.toAdd
  rw [carry_add_hom]

/-- The corresponding equality of cyclic second-cohomology classes. -/
theorem restriction_mk_set
    {m f : ℕ} [NeZero m] [NeZero f]
    {M : Type*} [CommGroup M]
    [MulDistribMulAction (Multiplicative (ZMod (m * f))) M]
    [MulDistribMulAction (Multiplicative (ZMod m)) M]
    (hsmul : ∀ g : Multiplicative (ZMod m), ∀ x : M,
      g • x = subgroupHom m f g • x)
    (pi : M)
    (hpi : ∀ g : Multiplicative (ZMod (m * f)), g • pi = pi) :
    MHTwo.restrictionHom (subgroupHom m f) hsmul
        (MHTwo.mk (factorSet pi hpi)) =
      MHTwo.mk
        (factorSet pi
          (fun g ↦ (hsmul g pi).trans (hpi (subgroupHom m f g)))) := by
  rw [MHTwo.restrictionHom_mk,
    restrict_set_subgroup hsmul pi hpi]

end

end Submission.CField.LBrauer.CCarry
