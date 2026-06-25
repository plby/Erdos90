import Towers.ClassField.Shifting.LowTateCohomology

/-!
# Milne, Class Field Theory, Theorem II.3.10: norm transitivity

For a normal subgroup `H`, the norm for `G` is the composite of the norm
for `H` and the norm for `G/H`.  This is the degree-zero calculation in the
solvable-group part of Milne's proof.
-/

namespace Towers.CField.Shifting

open Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The raw norm with codomain restricted to the invariant submodule. -/
noncomputable def normToInvariants
    {K V : Type u} [Group K] [Fintype K]
    [AddCommGroup V] [Module k V]
    (ρ : Representation k K V) : V →ₗ[k] ρ.invariants :=
  ρ.norm.codRestrict ρ.invariants fun x g => ρ.self_norm_apply g x

/-- The fiber of `G -> G/H` above the class of `g` is canonically a copy
of `H`, by right multiplication. -/
noncomputable def quotientFiberEquiv (H : Subgroup G) [H.Normal] (g : G) :
    {z : G // QuotientGroup.mk' H z = QuotientGroup.mk' H g} ≃ H where
  toFun z := ⟨g⁻¹ * z.1, QuotientGroup.eq.mp z.2.symm⟩
  invFun h := ⟨g * h.1, QuotientGroup.mk_mul_of_mem g h.2⟩
  left_inv z := Subtype.ext (by simp)
  right_inv h := Subtype.ext (by simp)

/-- The norm identity `N_G = N_{G/H} ∘ N_H`. -/
theorem norm_transitivity [Fintype G]
    (A : Rep.{u} k G) (H : Subgroup G) [H.Normal]
    [Fintype H] [Fintype (G ⧸ H)] (x : A) :
    ((A.ρ.quotientToInvariants H).norm
      ⟨(Rep.res H.subtype A).ρ.norm x,
        fun h => (Rep.res H.subtype A).ρ.self_norm_apply h x⟩).1 =
      A.ρ.norm x := by
  classical
  simp only [Representation.norm, LinearMap.sum_apply]
  rw [← Fintype.sum_fiberwise (QuotientGroup.mk' H)
    (fun g : G => A.ρ g x)]
  simp only [Submodule.coe_sum]
  apply Fintype.sum_congr
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
      rw [Representation.ofQuotient_coe_apply]
      calc
        _ = A.ρ g ((Rep.res H.subtype A).ρ.norm x) := by
          simp [Representation.toInvariants, Representation.subrepresentation,
            Representation.norm]
        _ = ∑ h : H, A.ρ (g * h.1) x := by
          simp [Representation.norm, ← Module.End.mul_apply, ← map_mul]
        _ = _ := by
          simpa [quotientFiberEquiv, ← Module.End.mul_apply, ← map_mul] using
            ((quotientFiberEquiv H g).symm.sum_comp
              (fun z => A.ρ z.1 x))

/-- Surjectivity of the subgroup and quotient norms implies surjectivity of
the ambient raw norm. -/
theorem invariants_surjective_normal
    [Fintype G] (A : Rep.{u} k G) (H : Subgroup G) [H.Normal]
    [Fintype H] [Fintype (G ⧸ H)]
    (hH : Function.Surjective
      (normToInvariants (Rep.res H.subtype A).ρ))
    (hQ : Function.Surjective
      (normToInvariants (A.ρ.quotientToInvariants H))) :
    Function.Surjective (normToInvariants A.ρ) := by
  intro x
  let xQ : (A.ρ.quotientToInvariants H).invariants :=
    ⟨⟨x.1, fun h => x.2 h.1⟩,
      fun q => QuotientGroup.induction_on q fun g =>
        Subtype.ext (by simpa using x.2 g)⟩
  obtain ⟨y, hy⟩ := hQ xQ
  obtain ⟨z, hz⟩ := hH y
  subst y
  refine ⟨z, Subtype.ext ?_⟩
  have hv := congrArg
    (fun w : (A.ρ.quotientToInvariants H).invariants => w.1.1) hy
  change A.ρ.norm z = x.1
  rw [← norm_transitivity A H z]
  simpa [normToInvariants, xQ] using hv

/-- Surjectivity of the norm from coinvariants is equivalent to vanishing
of degree-zero Tate cohomology. -/
theorem coinvariants_invariants_surjective
    [Fintype G] (A : Rep.{u} k G) :
    Function.Surjective (normCoinvariantsInvariants A) ↔
      Subsingleton (tateCohomologyZero A) := by
  rw [← LinearMap.range_eq_top, Submodule.Quotient.subsingleton_iff]

/-- Injectivity of the norm from coinvariants is equivalent to vanishing of
degree-minus-one Tate cohomology. -/
theorem norm_coinvariants_invariants
    [Fintype G] (A : Rep.{u} k G) :
    Function.Injective (normCoinvariantsInvariants A) ↔
      Subsingleton (tateCohomologyOne A) := by
  rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]

/-- Norm surjectivity is transitive across a normal subgroup. -/
theorem coinvariants_invariants_normal
    [Fintype G] (A : Rep.{u} k G) (H : Subgroup G) [H.Normal]
    [Fintype H] [Fintype (G ⧸ H)]
    (hH : Function.Surjective
      (normCoinvariantsInvariants (Rep.res H.subtype A)))
    (hQ : Function.Surjective
      (normCoinvariantsInvariants (A.quotientToInvariants H))) :
    Function.Surjective (normCoinvariantsInvariants A) := by
  have hHraw : Function.Surjective
      (normToInvariants (Rep.res H.subtype A).ρ) := by
    intro y
    obtain ⟨c, hc⟩ := hH y
    obtain ⟨z, rfl⟩ := Coinvariants.mk_surjective
      (Rep.res H.subtype A).ρ c
    exact ⟨z, hc⟩
  have hQraw : Function.Surjective
      (normToInvariants (A.ρ.quotientToInvariants H)) := by
    intro y
    obtain ⟨c, hc⟩ := hQ y
    obtain ⟨z, rfl⟩ := Coinvariants.mk_surjective
      (A.ρ.quotientToInvariants H) c
    exact ⟨z, hc⟩
  have hraw := invariants_surjective_normal A H hHraw hQraw
  intro y
  obtain ⟨z, hz⟩ := hraw y
  exact ⟨Coinvariants.mk A.ρ z, hz⟩

/-- Degree-zero Tate vanishing is transitive across a normal subgroup. -/
theorem subsingleton_cohomology_normal
    [Fintype G] (A : Rep.{u} k G) (H : Subgroup G) [H.Normal]
    [Fintype H] [Fintype (G ⧸ H)]
    (hH : Subsingleton
      (tateCohomologyZero (Rep.res H.subtype A)))
    (hQ : Subsingleton
      (tateCohomologyZero (A.quotientToInvariants H))) :
    Subsingleton (tateCohomologyZero A) :=
  (coinvariants_invariants_surjective A).1
    (coinvariants_invariants_normal A H
      ((coinvariants_invariants_surjective
        (Rep.res H.subtype A)).2 hH)
      ((coinvariants_invariants_surjective
        (A.quotientToInvariants H)).2 hQ))

end

end Towers.CField.Shifting
