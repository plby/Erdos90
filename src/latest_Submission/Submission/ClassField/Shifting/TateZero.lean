import Mathlib.Data.ZMod.QuotientGroup
import Submission.ClassField.Shifting.LowTateCohomology

/-!
# Milne, Class Field Theory, Lemma II.3.3(b): degree-zero Tate cohomology

For the trivial action of a finite group `G` on `ℤ`, the norm is
multiplication by `|G|`.  Consequently its degree-zero Tate cohomology is
`ℤ / |G|ℤ`, hence `ZMod |G|`.
-/

namespace Submission.CField.Shifting

open Representation

noncomputable section

variable (G : Type) [Group G] [Fintype G]

/-- Reduction modulo `|G|`, restricted to the invariant integers. -/
private def trivialZMod :
    (Rep.trivial ℤ G ℤ).ρ.invariants →+ ZMod (Fintype.card G) where
  toFun x := (x.1 : ZMod (Fintype.card G))
  map_zero' := by simp
  map_add' x y := by simp

private theorem trivial_z_surjective :
    Function.Surjective (trivialZMod G) := by
  intro z
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨⟨x, by simp [Representation.mem_invariants]⟩, by
    change (x : ZMod (Fintype.card G)) = x
    rfl⟩

/-- For the trivial action on `ℤ`, the image of the norm consists exactly
of the multiples of the cardinality of the group. -/
private theorem coinvariants_invariants_trivial
    (y : (Rep.trivial ℤ G ℤ).ρ.invariants) :
    y ∈ LinearMap.range
        (normCoinvariantsInvariants (Rep.trivial ℤ G ℤ)) ↔
      ∃ x : ℤ, y.1 = Fintype.card G • x := by
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Coinvariants.induction_on with
    | _ x =>
        refine ⟨x, ?_⟩
        change (Rep.trivial ℤ G ℤ).ρ.norm x = Fintype.card G • x
        simp [Representation.norm]
  · rintro ⟨x, hx⟩
    refine ⟨Coinvariants.mk (Rep.trivial ℤ G ℤ).ρ x, ?_⟩
    apply Subtype.ext
    change (Rep.trivial ℤ G ℤ).ρ.norm x = y.1
    simpa [Representation.norm] using hx.symm

private theorem coinvariants_invariants_int :
    (LinearMap.range
        (normCoinvariantsInvariants (Rep.trivial ℤ G ℤ))).toAddSubgroup =
      (trivialZMod G).ker := by
  ext y
  change y ∈ LinearMap.range
      (normCoinvariantsInvariants (Rep.trivial ℤ G ℤ)) ↔
    y ∈ (trivialZMod G).ker
  rw [coinvariants_invariants_trivial]
  rw [AddMonoidHom.mem_ker]
  change (∃ x : ℤ, y.1 = Fintype.card G • x) ↔
    (y.1 : ZMod (Fintype.card G)) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [nsmul_eq_mul, dvd_iff_exists_eq_mul_right]

/-- **Lemma II.3.3(b), first assertion.** For a finite group acting trivially
on `ℤ`, degree-zero Tate cohomology is `ℤ / |G|ℤ`. -/
noncomputable def tateCohomologyTrivial :
    tateCohomologyZero (Rep.trivial ℤ G ℤ) ≃+ ZMod (Fintype.card G) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (coinvariants_invariants_int G)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (trivialZMod G) (trivial_z_surjective G))

end

end Submission.CField.Shifting
