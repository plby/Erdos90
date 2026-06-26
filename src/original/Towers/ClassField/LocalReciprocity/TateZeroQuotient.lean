import Towers.ClassField.LocalFields.NormSubgroups
import Towers.ClassField.Shifting.LowTateCohomology
import Towers.ClassField.LocalBrauer.CohomologyTransport

/-!
# Tate degree zero as invariants modulo norms

For a finite multiplicative action, the representation-theoretic definition
of Tate degree zero is canonically the additive form of multiplicative
invariants modulo the group norm.  For a finite Galois extension this becomes
the field-unit quotient by the algebra norm.
-/

namespace Towers.CField.LRecip

noncomputable section

open Representation
open Towers.CField.LFTheory
open Towers.CField.Shifting
open Towers.CField.LBrauer

variable (G M : Type) [Group G] [Fintype G]
  [CommGroup M] [MulDistribMulAction G M]

/-- Convert a representation invariant in the additive model back to a
multiplicative invariant. -/
private def repInvariantMul
    (x : (Rep.ofMulDistribMulAction G M).ρ.invariants) :
    FMAct.invariants G M :=
  ⟨x.1.toMul, fun g ↦ congrArg Additive.toMul (x.2 g)⟩

/-- The quotient map from representation invariants to multiplicative
invariants modulo norms, written additively. -/
private def repInvariantQuotient :
    (Rep.ofMulDistribMulAction G M).ρ.invariants →+
      Additive (FMAct.invariantsModNorm G M) where
  toFun x := Additive.ofMul
    (QuotientGroup.mk' (FMAct.norm G M).range
      (repInvariantMul G M x))
  map_zero' := by
    apply Additive.toMul.injective
    apply (QuotientGroup.eq_one_iff _).2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [repInvariantMul, FMAct.norm]
    rfl
  map_add' x y := by
    apply Additive.toMul.injective
    rfl

private theorem rep_invariant_surjective :
    Function.Surjective (repInvariantQuotient G M) := by
  intro q
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (FMAct.norm G M).range q.toMul
  let x : (Rep.ofMulDistribMulAction G M).ρ.invariants :=
    ⟨Additive.ofMul y.1, fun g ↦ congrArg Additive.ofMul (y.2 g)⟩
  refine ⟨x, ?_⟩
  apply Additive.toMul.injective
  exact hy

private theorem rep_invariant_norm (x : M) :
    repInvariantMul G M
        (normCoinvariantsInvariants (Rep.ofMulDistribMulAction G M)
          (Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ
            (Additive.ofMul x))) =
      FMAct.norm G M x := by
  apply Subtype.ext
  change Additive.toMul
      ((Rep.ofMulDistribMulAction G M).ρ.norm (Additive.ofMul x)) =
    ∏ g : G, g • x
  simp only [Representation.norm]
  rw [LinearMap.sum_apply]
  change Additive.toMul
      (∑ g ∈ (Finset.univ : Finset G),
        (Additive.ofMul (g • x) : Additive M)) =
    ∏ g ∈ (Finset.univ : Finset G), g • x
  rw [toMul_sum]
  rfl

private theorem range_rep_invariant :
    (LinearMap.range
        (normCoinvariantsInvariants
          (Rep.ofMulDistribMulAction G M))).toAddSubgroup =
      (repInvariantQuotient G M).ker := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Coinvariants.induction_on with
    | _ y =>
        apply AddMonoidHom.mem_ker.mpr
        apply Additive.toMul.injective
        change QuotientGroup.mk' (FMAct.norm G M).range
            (repInvariantMul G M
              (normCoinvariantsInvariants
                (Rep.ofMulDistribMulAction G M)
                (Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ y))) = 1
        have hnorm := rep_invariant_norm G M y.toMul
        calc
          QuotientGroup.mk' (FMAct.norm G M).range
              (repInvariantMul G M
                (normCoinvariantsInvariants
                  (Rep.ofMulDistribMulAction G M)
                  (Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ y))) =
              QuotientGroup.mk' (FMAct.norm G M).range
                (FMAct.norm G M y.toMul) := by
                  simpa using congrArg
                    (QuotientGroup.mk' (FMAct.norm G M).range) hnorm
          _ = 1 := (QuotientGroup.eq_one_iff _).2 ⟨y.toMul, rfl⟩
  · intro hx
    have hxq : QuotientGroup.mk' (FMAct.norm G M).range
        (repInvariantMul G M x) = 1 := by
      exact congrArg Additive.toMul (AddMonoidHom.mem_ker.mp hx)
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1 hxq
    refine ⟨Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ
      (Additive.ofMul y), ?_⟩
    apply Subtype.ext
    have hnorm := rep_invariant_norm G M y
    exact congrArg Additive.ofMul
      ((congrArg Subtype.val hnorm).trans (congrArg Subtype.val hy))

/-- Tate degree zero of a multiplicative representation is multiplicative
invariants modulo norms, with the quotient written additively. -/
noncomputable def tateCohomologyInvariants :
    tateCohomologyZero (Rep.ofMulDistribMulAction G M) ≃+
      Additive (FMAct.invariantsModNorm G M) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (range_rep_invariant G M)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (repInvariantQuotient G M)
      (rep_invariant_surjective G M))

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- Base-field units are exactly the units fixed by the Galois group. -/
private def baseGaloisInvariants :
    Kˣ →* FMAct.invariants Gal(L/K) Lˣ where
  toFun x := ⟨Units.map (algebraMap K L) x, by
    intro sigma
    apply Units.ext
    simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private theorem base_invariants_bijective :
    Function.Bijective (baseGaloisInvariants K L) := by
  constructor
  · intro x y hxy
    apply Units.ext
    apply (algebraMap K L).injective
    have h := congrArg
      (fun z : FMAct.invariants Gal(L/K) Lˣ ↦ ((z.1 : Lˣ) : L)) hxy
    simpa [baseGaloisInvariants] using h
  · intro x
    have hfixed : ∀ sigma : Gal(L/K), sigma (x.1 : L) = (x.1 : L) := by
      intro sigma
      exact congrArg Units.val (x.2 sigma)
    obtain ⟨a, ha⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed
        (F := K) (E := L) (x.1 : L)).2 hfixed
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, map_zero] at ha
      exact x.1.ne_zero ha.symm
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact ha

private noncomputable def baseUnitsInvariants :
    Kˣ ≃* FMAct.invariants Gal(L/K) Lˣ :=
  MulEquiv.ofBijective (baseGaloisInvariants K L)
    (base_invariants_bijective K L)

private theorem base_units_invariants (x : Lˣ) :
    baseUnitsInvariants K L (normOnUnits K L x) =
      FMAct.norm Gal(L/K) Lˣ x := by
  apply Subtype.ext
  apply Units.ext
  simpa [baseUnitsInvariants,
    baseGaloisInvariants, normOnUnits, FMAct.norm] using
      (Algebra.norm_eq_prod_automorphisms K (x : L))

private theorem galois_comap_units :
    (FMAct.norm Gal(L/K) Lˣ).range ≤
      (normOnUnits K L).range.comap
        (baseUnitsInvariants K L).symm.toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  exact (baseUnitsInvariants K L).eq_symm_apply.mpr
    (base_units_invariants K L x)

private theorem base_comap_units :
    (normOnUnits K L).range ≤
      (FMAct.norm Gal(L/K) Lˣ).range.comap
        (baseUnitsInvariants K L).toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x, (base_units_invariants K L x).symm⟩

/-- Galois invariants modulo the group norm are base-field units modulo the
field norm. -/
noncomputable def galoisInvariantsMod :
    FMAct.invariantsModNorm Gal(L/K) Lˣ ≃*
      Kˣ ⧸ normSubgroup K L where
  toFun := QuotientGroup.map
    (FMAct.norm Gal(L/K) Lˣ).range
    (normOnUnits K L).range
    (baseUnitsInvariants K L).symm.toMonoidHom
    (galois_comap_units K L)
  invFun := QuotientGroup.map
    (normOnUnits K L).range
    (FMAct.norm Gal(L/K) Lˣ).range
    (baseUnitsInvariants K L).toMonoidHom
    (base_comap_units K L)
  left_inv q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (FMAct.norm Gal(L/K) Lˣ).range q
    apply congrArg (QuotientGroup.mk'
      (FMAct.norm Gal(L/K) Lˣ).range)
    exact (baseUnitsInvariants K L).apply_symm_apply x
  right_inv q := by
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (normOnUnits K L).range q
    apply congrArg (QuotientGroup.mk' (normOnUnits K L).range)
    exact (baseUnitsInvariants K L).symm_apply_apply x
  map_mul' x y := map_mul _ x y

@[simp]
theorem galois_invariants_algebra
    (x : Kˣ) :
    galoisInvariantsMod K L
        (QuotientGroup.mk'
          (FMAct.norm Gal(L/K) Lˣ).range
          ⟨Units.map (algebraMap K L) x, by
            intro sigma
            apply Units.ext
            exact sigma.commutes x⟩) =
      QuotientGroup.mk' (normSubgroup K L) x := by
  change QuotientGroup.mk' (normSubgroup K L)
      ((baseUnitsInvariants K L).symm
        (baseUnitsInvariants K L x)) = _
  rw [MulEquiv.symm_apply_apply]

/-- For a finite Galois extension, Tate degree zero is the additive form of
the field-unit norm quotient. -/
noncomputable def galoisTateQuotient :
    tateCohomologyZero (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) ≃+
      Additive (Kˣ ⧸ normSubgroup K L) :=
  (tateCohomologyInvariants Gal(L/K) Lˣ).trans
    (galoisInvariantsMod K L).toAdditive

end Galois

end

end Towers.CField.LRecip
