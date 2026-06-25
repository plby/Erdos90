import Towers.ClassField.LocalBrauer.CanonicalUnramifiedData
import Towers.ClassField.LocalBrauer.CohomologyTransport


/-!
# Vanishing of unit-valued H2 for unramified extensions

For a finite unramified extension, invariant integer units are exactly the
base integer units, and the finite-action norm agrees with the integer-unit
field norm.  Norm surjectivity therefore makes the invariants-modulo-norm
group trivial.  The cyclic `H²` calculation gives Milne's Proposition IV.4.3
for every positive canonical unramified level.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open CProduca

attribute [local instance] Units.mulDistribMulActionRight

namespace FLExt

variable (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]

/-- The spectral valuative relation on `L` extends the one on `K`. -/
@[implicit_reducible]
noncomputable def valuativeSpectralExtension :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  constructor
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation K)
    (NormedField.valuation (K := K))).trans
      ((Valuation.HasExtension.val_isEquiv_comap
        (vR := NormedField.valuation (K := K))
        (vA := NormedField.valuation (K := L))).trans
          ((ValuativeRel.isEquiv (ValuativeRel.valuation L)
            (NormedField.valuation (K := L))).symm.comap
              (algebraMap K L)))

set_option maxHeartbeats 1200000 in
-- The dependent spectral local-field structure makes kernel checking unusually expensive.
omit [IsGalois K L] in
/-- The valuation-relation integers of the spectral local-field structure
are the integral closure of the base valuation-relation integers. -/
theorem valuative_spectral_closure :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    IsIntegralClosure 𝒪[L] 𝒪[K] L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  let N := Valuation.integer (NormedField.valuation (K := L))
  letI : Algebra 𝒪[K] N := valuativeSpectralAlgebra K L
  letI : IsScalarTower 𝒪[K] N L :=
    valuativeSpectralTower K L
  letI : IsIntegralClosure N 𝒪[K] L :=
    spectral_integer_valuative K L
  constructor
  · exact Subtype.coe_injective
  · intro x
    rw [IsIntegralClosure.isIntegral_iff (A := N)]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨⟨y.1, ?_⟩, hy⟩
      have hmem := congrArg
        (fun S : Subring L ↦ (y.1 : L) ∈ S)
        (valuative_integer_norm L)
      exact hmem.symm.mp y.2
    · rintro ⟨y, hy⟩
      refine ⟨⟨y.1, ?_⟩, hy⟩
      have hmem := congrArg
        (fun S : Subring L ↦ (y.1 : L) ∈ S)
        (valuative_integer_norm L)
      exact hmem.mp y.2

/-- The natural Galois action on the spectral valuation integers. -/
@[implicit_reducible]
noncomputable def integerGaloisAction :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L := nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := valuativeRel K L
    MulSemiringAction Gal(L/K) 𝒪[L] := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L := nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) := valuativeSpectralExtension K L
  letI : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    valuative_spectral_closure K L
  exact IsIntegralClosure.MulSemiringAction 𝒪[K] K L 𝒪[L]

end FLExt

section FixedUnits

variable {A B G : Type*} [CommRing A] [CommRing B] [Group G] [Fintype G]
  [MulSemiringAction G B] [Algebra A B] [IsGaloisGroup G A B]

/-- Base units, regarded as invariant units upstairs. -/
private def baseInvariants :
    Aˣ →* FMAct.invariants G Bˣ where
  toFun x := ⟨Units.map (algebraMap A B) x, by
    intro g
    apply Units.ext
    simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

variable [FaithfulSMul A B] [IsLocalHom (algebraMap A B)]

omit [Fintype G] in
private theorem units_invariants_bijective :
    Function.Bijective (baseInvariants (A := A) (B := B) (G := G)) := by
  constructor
  · intro x y hxy
    apply Units.ext
    apply (FaithfulSMul.algebraMap_injective A B)
    have h := congrArg
      (fun z : FMAct.invariants G Bˣ ↦ ((z.1 : Bˣ) : B)) hxy
    simpa [baseInvariants] using h
  · intro x
    have hfixed : ∀ g : G, g • (x.1 : B) = (x.1 : B) := by
      intro g
      exact congrArg Units.val (x.2 g)
    obtain ⟨a, ha⟩ :=
      Algebra.IsInvariant.isInvariant (A := A) (B := B) (G := G)
        (x.1 : B) hfixed
    have haUnit : IsUnit a := by
      rw [← isUnit_map_iff (algebraMap A B) a, ha]
      exact x.1.isUnit
    refine ⟨haUnit.unit, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change algebraMap A B (haUnit.unit : A) = (x.1 : B)
    rw [haUnit.unit_spec, ha]

/-- Base units are multiplicatively equivalent to invariant upstairs units. -/
private noncomputable def baseMulInvariants :
    Aˣ ≃* FMAct.invariants G Bˣ :=
  MulEquiv.ofBijective (baseInvariants (A := A) (B := B) (G := G))
    units_invariants_bijective

private theorem action_surjective_base
    (N : Bˣ →* Aˣ) (hN : Function.Surjective N)
    (hprod : ∀ v : Bˣ,
      algebraMap A B (N v : A) = ∏ g : G, g • (v : B)) :
    Function.Surjective (FMAct.norm G Bˣ) := by
  intro y
  obtain ⟨v, hv⟩ := hN ((baseMulInvariants
    (A := A) (B := B) (G := G)).symm y)
  refine ⟨v, ?_⟩
  apply Subtype.ext
  rw [FMAct.norm_coe]
  apply Units.ext
  change ((∏ g : G, g • v : Bˣ) : B) = (y.1 : Bˣ)
  rw [Units.coe_prod]
  change (∏ g : G, g • (v : B)) = (y.1 : Bˣ)
  rw [← hprod, hv]
  exact congrArg
    (fun z : FMAct.invariants G Bˣ ↦ ((z.1 : Bˣ) : B))
    ((baseMulInvariants
      (A := A) (B := B) (G := G)).apply_symm_apply y)

end FixedUnits

section AbstractH2

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M]
  [MulDistribMulAction G M]

omit [Fintype G] in
private theorem multiplicative_h_subsingleton
    [Subsingleton G] : Subsingleton (MHTwo G M) := by
  constructor
  intro x y
  obtain ⟨c, rfl⟩ := MHTwo.exists_mk_eq x
  obtain ⟨d, rfl⟩ := MHTwo.exists_mk_eq y
  apply congrArg MHTwo.mk
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  have hg : g = 1 := Subsingleton.elim _ _
  rw [hg, c.map_one_fst, d.map_one_fst]

private theorem cyclic_multiplicative_subsingleton
    {n : ℕ} [NeZero n] (hn : 1 < n)
    (e : Multiplicative (ZMod n) ≃* G)
    (hN : Function.Surjective (FMAct.norm G M)) :
    Subsingleton (MHTwo G M) := by
  let eH2 : MHTwo G M ≃*
      FMAct.invariantsModNorm G M :=
    GroupH2.mulInvariantsMod (M := M) e hn
  have hrange : (FMAct.norm G M).range = ⊤ :=
    MonoidHom.range_eq_top.mpr hN
  have hquot : Subsingleton (FMAct.invariantsModNorm G M) := by
    change Subsingleton
      (FMAct.invariants G M ⧸ (FMAct.norm G M).range)
    rw [hrange]
    exact QuotientGroup.subsingleton_quotient_top
  exact ⟨fun x y ↦ eH2.injective (@Subsingleton.elim _ hquot _ _)⟩

end AbstractH2

set_option maxHeartbeats 1200000 in
-- The spectral integer action makes the norm comparison instance-heavy.
/-- A cyclic finite local extension whose norm is surjective on valuation-ring
units has trivial unit-valued multiplicative `H²`.

This is the abstract cohomological part of Proposition IV.4.3.  Unramifiedness
enters only through the separate theorem that the unit norm is surjective. -/
theorem integer_subsingleton_surjective
    (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]
    (n : ℕ) [NeZero n]
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K))
    (hNorm :
      letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
      letI : NontriviallyNormedField L :=
        FLExt.nontriviallyNormedField K L
      letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
      letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
      letI : ValuativeRel L := FLExt.valuativeRel K L
      Function.Surjective (FLExt.integerUnitNorm K L)) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L := FLExt.valuativeRel K L
    letI : MulSemiringAction Gal(L/K) 𝒪[L] :=
      FLExt.integerGaloisAction K L
    Subsingleton (MHTwo Gal(L/K) 𝒪[L]ˣ) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L := FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    FLExt.nonarchimedeanLocalField K L
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) :=
    spectralValuationExtension K L
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation L) :=
    FLExt.valuativeSpectralExtension K L
  let A := 𝒪[K]
  let B := 𝒪[L]
  let G := Gal(L/K)
  letI : MulSemiringAction G B :=
    FLExt.integerGaloisAction K L
  letI : IsIntegralClosure B A L :=
    FLExt.valuative_spectral_closure K L
  letI : Algebra.IsIntegral A B :=
    IsIntegralClosure.isIntegral_algebra A L
  letI : IsGaloisGroup G A B :=
    IsGaloisGroup.of_isFractionRing G A B K L
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).2 <| by
      intro x y hxy
      apply Subtype.ext
      apply (algebraMap K L).injective
      simpa only [IsScalarTower.algebraMap_apply] using
        congrArg (algebraMap B L) hxy
  have hprod (v : Bˣ) :
      algebraMap A B
          (FLExt.integerUnitNorm K L v : A) =
        ∏ g : G, g • (v : B) := by
    apply IsFractionRing.injective B L
    calc
      algebraMap B L (algebraMap A B
          (FLExt.integerUnitNorm K L v : A)) =
          algebraMap K L (Algebra.norm K (v : L)) := by
        change algebraMap K L
            (((FLExt.integerUnitNorm K L v : A) : K)) =
          algebraMap K L (Algebra.norm K (v : L))
        rw [FLExt.integer_norm_coe]
      _ = ∏ g : G, g (v : L) :=
        Algebra.norm_eq_prod_automorphisms K (v : L)
      _ = algebraMap B L (∏ g : G, g • (v : B)) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro g _
        exact (algebraMap.coe_smul' (B := B) (C := L) g (v : B)).symm
  have hActionNorm : Function.Surjective (FMAct.norm G Bˣ) :=
    action_surjective_base
      (A := A) (B := B) (G := G)
      (FLExt.integerUnitNorm K L) hNorm hprod
  by_cases hn : n = 1
  · subst n
    letI : Subsingleton G := eGal.symm.injective.subsingleton
    exact multiplicative_h_subsingleton
  · have hn' : 1 < n := (Nat.one_lt_iff_ne_zero_and_ne_one).2
      ⟨NeZero.ne n, hn⟩
    exact cyclic_multiplicative_subsingleton
      hn' eGal hActionNorm

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

set_option maxHeartbeats 1200000 in
-- The canonical local-data theorem transports a dependent explicit model.
/-- **Milne, Proposition IV.4.3.** Integer-unit-valued multiplicative `H²`
vanishes at every positive canonical unramified level. -/
theorem level_integer_subsingleton
    (n : ℕ) [NeZero n] :
    let E := canonicalUnramifiedLevel K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      FLExt.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E := FLExt.valuativeRel K E
    letI : MulSemiringAction Gal(E/K) 𝒪[E] :=
      FLExt.integerGaloisAction K E
    Subsingleton (MHTwo Gal(E/K) 𝒪[E]ˣ) := by
  let E := canonicalUnramifiedLevel K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    spectralValuationExtension K E
  letI : (ValuativeRel.valuation K).HasExtension
      (ValuativeRel.valuation E) :=
    FLExt.valuativeSpectralExtension K E
  let A := 𝒪[K]
  let B := 𝒪[E]
  let G := Gal(E/K)
  letI : MulSemiringAction G B :=
    FLExt.integerGaloisAction K E
  letI : IsIntegralClosure B A E :=
    FLExt.valuative_spectral_closure K E
  letI : Algebra.IsIntegral A B :=
    IsIntegralClosure.isIntegral_algebra A E
  letI : IsGaloisGroup G A B :=
    IsGaloisGroup.of_isFractionRing G A B K E
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).2 <| by
      intro x y hxy
      apply Subtype.ext
      apply (algebraMap K E).injective
      simpa only [IsScalarTower.algebraMap_apply] using
        congrArg (algebraMap B E) hxy
  obtain ⟨hResidueAlgebra, hUnit, _horder, _hfinite, _hunramified⟩ :=
    unramified_level_data K n
  letI : Algebra 𝓀[K] 𝓀[E] := hResidueAlgebra
  let hLocal : UnramifiedLocalData K E
      (FLExt.integerUnitNorm K E) :=
    FLExt.unramified_data_unit
      K E hResidueAlgebra hUnit
  have hNorm : Function.Surjective
      (FLExt.integerUnitNorm K E) :=
    unramified_units_surjective K E
      (FLExt.integerUnitNorm K E) hLocal
  have hprod (v : Bˣ) :
      algebraMap A B
          (FLExt.integerUnitNorm K E v : A) =
        ∏ g : G, g • (v : B) := by
    apply IsFractionRing.injective B E
    calc
      algebraMap B E (algebraMap A B
          (FLExt.integerUnitNorm K E v : A)) =
          algebraMap K E (Algebra.norm K (v : E)) := by
        change algebraMap K E
            (((FLExt.integerUnitNorm K E v : A) : K)) =
          algebraMap K E (Algebra.norm K (v : E))
        rw [FLExt.integer_norm_coe]
      _ = ∏ g : G, g (v : E) :=
        Algebra.norm_eq_prod_automorphisms K (v : E)
      _ = algebraMap B E (∏ g : G, g • (v : B)) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro g _
        exact (algebraMap.coe_smul' (B := B) (C := E) g (v : B)).symm
  have hActionNorm : Function.Surjective (FMAct.norm G Bˣ) :=
    action_surjective_base
      (A := A) (B := B) (G := G)
      (FLExt.integerUnitNorm K E) hNorm hprod
  let eGal := galZMod K n
  by_cases hn : n = 1
  · subst n
    letI : Subsingleton G := eGal.symm.injective.subsingleton
    exact multiplicative_h_subsingleton
  · have hn' : 1 < n := (Nat.one_lt_iff_ne_zero_and_ne_one).2
      ⟨NeZero.ne n, hn⟩
    exact cyclic_multiplicative_subsingleton
      hn' eGal hActionNorm

end

end Towers.CField.LBrauer
