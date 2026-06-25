import Towers.ClassField.LocalBrauer.CanonicalAutomorphismExt
import Towers.ClassField.LocalBrauer.MixedUniverseChange
import Towers.ClassField.LocalBrauer.FieldAdicOrder

/-!
# Canonical unramified towers under a change of universe

This file supplies the local-field input left by the mixed Brauer reduction:
an isometric equivalence of base fields preserves the residue cardinal and
the Frobenius polynomials defining the canonical unramified tower.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u v

open ValuativeRel
open Towers.CField.LFTheory
open scoped NormedField Valued

/-- Mapping the coefficients of a polynomial along an isometric ring
equivalence does not change its spectral value. -/
theorem spectral_value_norm
    {R S : Type*} [SeminormedRing R] [SeminormedRing S]
    (e : R ≃+* S) (hnorm : ∀ x : R, ‖e x‖ = ‖x‖)
    (p : Polynomial R) :
    spectralValue (p.map e.toRingHom) = spectralValue p := by
  unfold spectralValue
  congr 1
  funext i
  unfold spectralValueTerms
  rw [Polynomial.natDegree_map_eq_of_injective e.injective]
  simp only [Polynomial.coeff_map, RingEquiv.toRingHom_eq_coe]
  by_cases hi : i < p.natDegree
  · simp only [if_pos hi]
    change ‖e (p.coeff i)‖ ^ _ = _
    rw [hnorm]
  · simp only [if_neg hi]

variable (k : Type v) (K : Type u)
  [NontriviallyNormedField k] [IsUltrametricDist k] [ValuativeRel k]
  [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Algebra k K]

/-- An isometric base-field equivalence restricts to the integer rings
defined by the norm valuations. -/
noncomputable def integerRingAlg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖) :
    Valuation.integer (NormedField.valuation (K := k)) ≃+*
      Valuation.integer (NormedField.valuation (K := K)) :=
  RingEquiv.restrict e.symm.toRingEquiv _ _ fun x => by
    simp only [Valuation.mem_integer_iff, NormedField.valuation_apply]
    rw [← NNReal.coe_le_coe]
    change ‖x‖ ≤ 1 ↔ ‖e.symm x‖ ≤ 1
    rw [hnorm]

/-- The same equivalence on the valuation-relation integer rings used by
the canonical unramified construction. -/
noncomputable def valuativeIntegerAlg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖) :
    Valuation.integer (ValuativeRel.valuation k) ≃+*
      Valuation.integer (ValuativeRel.valuation K) :=
  (valuativeIntegerNorm k).trans
    ((integerRingAlg k K e hnorm).trans
      (valuativeIntegerNorm K).symm)

/-- An isometric base-field equivalence induces an equivalence of residue
fields. -/
noncomputable def localResidueAlg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖) :
    Valued.ResidueField k ≃+* Valued.ResidueField K :=
  IsLocalRing.ResidueField.mapEquiv
    (integerRingAlg k K e hnorm)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The residue cardinal used in the canonical unramified tower is invariant
under an isometric field equivalence. -/
theorem local_residue_alg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖) :
    localResidueCard k = localResidueCard K := by
  exact Nat.card_congr
    (localResidueAlg k K e hnorm).toEquiv

/-- An isometric equivalence of local fields preserves comparisons between
their normalized integer-valued orders. -/
theorem local_order_alg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (x y : kˣ) :
    localUnitOrder k (Additive.ofMul x) ≤
        localUnitOrder k (Additive.ofMul y) ↔
      localUnitOrder K
          (Additive.ofMul (Units.map e.symm.toRingEquiv.toMonoidHom x)) ≤
        localUnitOrder K
          (Additive.ofMul (Units.map e.symm.toRingEquiv.toMonoidHom y)) := by
  rw [local_order_valuation,
    local_order_valuation]
  rw [← Valuation.vle_iff_le (ValuativeRel.valuation k),
    ← Valuation.vle_iff_le (ValuativeRel.valuation K),
    Valuation.vle_iff_le (NormedField.valuation (K := k)),
    Valuation.vle_iff_le (NormedField.valuation (K := K))]
  simp only [NormedField.valuation_apply]
  have hnormNN (z : k) : ‖e.symm z‖₊ = ‖z‖₊ := by
    apply NNReal.eq
    exact hnorm z
  change ‖(y : k)‖₊ ≤ ‖(x : k)‖₊ ↔
    ‖e.symm (y : k)‖₊ ≤ ‖e.symm (x : k)‖₊
  rw [hnormNN, hnormNN]

/-- The strict-order version of
`local_order_alg`. -/
theorem local_alg_equiv
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (x y : kˣ) :
    localUnitOrder k (Additive.ofMul x) <
        localUnitOrder k (Additive.ofMul y) ↔
      localUnitOrder K
          (Additive.ofMul (Units.map e.symm.toRingEquiv.toMonoidHom x)) <
        localUnitOrder K
          (Additive.ofMul (Units.map e.symm.toRingEquiv.toMonoidHom y)) := by
  rw [lt_iff_not_ge, lt_iff_not_ge,
    local_order_alg k K e hnorm y x]

/-- An isometric equivalence of local fields preserves the normalized
integer-valued order exactly.  The earlier comparison lemmas determine the
orientation, while surjectivity of both order maps rules out a nontrivial
positive rescaling. -/
theorem order_alg_equiv
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (x : kˣ) :
    localUnitOrder K
        (Additive.ofMul
          (Units.map e.symm.toRingEquiv.toMonoidHom x)) =
      localUnitOrder k (Additive.ofMul x) := by
  let mapUnits : kˣ ≃* Kˣ := Units.mapEquiv e.symm.toMulEquiv
  let mapAdd : Additive kˣ ≃+ Additive Kˣ := mapUnits.toAdditive
  let transported : Additive kˣ →+ ℤ :=
    (localUnitOrder K).comp mapAdd.toAddMonoidHom
  have htransported : Function.Surjective transported :=
    (local_order_surjective K).comp mapAdd.surjective
  have heq : localUnitOrder k = transported := by
    apply surjective_add_hom
      (localUnitOrder k) transported
      (local_order_surjective k) htransported
    intro a b
    change localUnitOrder k a ≤ localUnitOrder k b ↔
      localUnitOrder K (mapAdd a) ≤ localUnitOrder K (mapAdd b)
    simpa [mapAdd, mapUnits] using
      (local_order_alg k K e hnorm
        a.toMul b.toMul)
  have hx := DFunLike.congr_fun heq (Additive.ofMul x)
  exact hx.symm

/-- The image of the chosen source uniformizer under an isometric local-field
equivalence still has normalized order one. -/
theorem mapped_uniformizer_alg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖) :
    localUnitOrder K
        (Additive.ofMul
          (Units.map e.symm.toRingEquiv.toMonoidHom
            (canonicalLocalUniformizer k))) = 1 := by
  let mapUnits : kˣ →* Kˣ := Units.map e.symm.toRingEquiv.toMonoidHom
  let u := canonicalLocalUniformizer k
  have hkOne :
      localUnitOrder k (Additive.ofMul (1 : kˣ)) = 0 := by
    change localUnitOrder k (0 : Additive kˣ) = 0
    exact map_zero (localUnitOrder k)
  have hKOne :
      localUnitOrder K (Additive.ofMul (1 : Kˣ)) = 0 := by
    change localUnitOrder K (0 : Additive Kˣ) = 0
    exact map_zero (localUnitOrder K)
  have huPos :
      localUnitOrder k (Additive.ofMul (1 : kˣ)) <
        localUnitOrder k (Additive.ofMul u) := by
    rw [hkOne, show localUnitOrder k (Additive.ofMul u) = 1 by
      exact canonical_uniformizer_order k]
    norm_num
  have hmapUPos :=
    (local_alg_equiv k K e hnorm (1 : kˣ) u).mp huPos
  have hmapUPos' :
      0 < localUnitOrder K (Additive.ofMul (mapUnits u)) := by
    rw [map_one, hKOne] at hmapUPos
    change 0 < localUnitOrder K (Additive.ofMul (mapUnits u)) at hmapUPos
    exact hmapUPos
  let x : kˣ := Units.map e.toRingEquiv.toMonoidHom
    (canonicalLocalUniformizer K)
  have hmapX : mapUnits x = canonicalLocalUniformizer K := by
    apply Units.ext
    change e.symm (e (canonicalLocalUniformizer K : K)) = _
    exact e.symm_apply_apply _
  have htargetPos :
      localUnitOrder K (Additive.ofMul (1 : Kˣ)) <
        localUnitOrder K (Additive.ofMul (mapUnits x)) := by
    rw [hKOne, hmapX, canonical_uniformizer_order]
    norm_num
  have hxPos :=
    (local_alg_equiv k K e hnorm (1 : kˣ) x).mpr
      (by simpa [mapUnits] using htargetPos)
  have hxPos' : 0 < localUnitOrder k (Additive.ofMul x) := by
    rw [hkOne] at hxPos
    exact hxPos
  have hux :
      localUnitOrder k (Additive.ofMul u) ≤
        localUnitOrder k (Additive.ofMul x) := by
    rw [show localUnitOrder k (Additive.ofMul u) = 1 by
      exact canonical_uniformizer_order k]
    omega
  have hmapULe :=
    (local_order_alg k K e hnorm u x).mp hux
  have hmapULe' :
      localUnitOrder K (Additive.ofMul (mapUnits u)) ≤ 1 := by
    change localUnitOrder K (Additive.ofMul (mapUnits u)) ≤
      localUnitOrder K (Additive.ofMul (mapUnits x)) at hmapULe
    rw [hmapX, canonical_uniformizer_order] at hmapULe
    exact hmapULe
  change localUnitOrder K (Additive.ofMul (mapUnits u)) = 1
  omega

omit [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The defining Frobenius polynomial is carried to the corresponding
polynomial over the equivalent field. -/
theorem local_frobenius_alg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) :
    (localFrobeniusPolynomial k n).map e.symm.toRingEquiv.toRingHom =
      localFrobeniusPolynomial K n := by
  simp [localFrobeniusPolynomial,
    local_residue_alg k K e hnorm]

/-- Regard the source canonical unramified level as an algebra over the
equivalent target base field. -/
@[implicit_reducible]
noncomputable def levelTransportedAlgebra
    (e : K ≃ₐ[k] k) (n : ℕ) :
    Algebra K (canonicalUnramifiedLevel k n) :=
  ((algebraMap k (canonicalUnramifiedLevel k n)).comp
    e.toRingEquiv.toRingHom).toAlgebra

set_option maxHeartbeats 1000000 in
-- Finite/Galois transport and the splitting-field uniqueness proof elaborate together.
set_option synthInstance.maxHeartbeats 200000 in
/-- The canonical degree-`n` unramified levels of isometric equivalent local
fields are equivalent over the target base field, after transporting the
source algebra structure. -/
noncomputable def canonicalLevelAlg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) [NeZero n] :
    letI : Algebra K (canonicalUnramifiedLevel k n) :=
      levelTransportedAlgebra k K e n
    canonicalUnramifiedLevel k n ≃ₐ[K]
      canonicalUnramifiedLevel K n := by
  let U := canonicalUnramifiedLevel k n
  letI : Algebra K U :=
    levelTransportedAlgebra k K e n
  have hsquare :
      (algebraMap K U).comp e.symm.toRingEquiv.toRingHom =
        (RingEquiv.refl U).toRingHom.comp (algebraMap k U) := by
    apply RingHom.ext
    intro x
    change algebraMap k U (e (e.symm x)) = algebraMap k U x
    rw [e.apply_symm_apply]
  letI : Module.Finite K U :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl U) hsquare
  letI : IsGalois K U := IsGalois.of_equiv_equiv
    (F := k) (E := U) (M := K) (N := U)
    (f := e.symm.toRingEquiv) (g := RingEquiv.refl U) hsquare
  have hdegree : Module.finrank K U = n := by
    calc
      Module.finrank K U = Module.finrank k U :=
        (Algebra.finrank_eq_of_equiv_equiv
          e.symm.toRingEquiv (RingEquiv.refl U) hsquare).symm
      _ = n := unramified_level_finrank k n
  have hsplit :
      ((localFrobeniusPolynomial K n).map (algebraMap K U)).Splits := by
    have hcomp : (algebraMap K U).comp e.symm.toRingEquiv.toRingHom =
        algebraMap k U := by
      simpa using hsquare
    rw [← local_frobenius_alg k K e hnorm,
      Polynomial.map_map, hcomp]
    exact unramified_level_splits k n
  exact Classical.choice
    (alg_level_splits K U n hdegree hsplit)

/-- The underlying ring equivalence between canonical unramified levels. -/
noncomputable def unramifiedLevelAlg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) [NeZero n] :
    canonicalUnramifiedLevel k n ≃+*
      canonicalUnramifiedLevel K n := by
  letI : Algebra K (canonicalUnramifiedLevel k n) :=
    levelTransportedAlgebra k K e n
  exact (canonicalLevelAlg
    k K e hnorm n).toRingEquiv

/-- The canonical-level equivalence extends the original base-field
equivalence. -/
theorem level_alg_algebra
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) [NeZero n] (x : k) :
    unramifiedLevelAlg k K e hnorm n
        (algebraMap k (canonicalUnramifiedLevel k n) x) =
      algebraMap K (canonicalUnramifiedLevel K n) (algebraMap k K x) := by
  letI : Algebra K (canonicalUnramifiedLevel k n) :=
    levelTransportedAlgebra k K e n
  have h := (canonicalLevelAlg
    k K e hnorm n).commutes (algebraMap k K x)
  simpa [unramifiedLevelAlg,
    levelTransportedAlgebra,
    RingHom.algebraMap_toAlgebra] using h

/-- The base and canonical degree-`n` level equivalences form a commuting
square. -/
theorem level_alg_square
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) [NeZero n] :
    (algebraMap K (canonicalUnramifiedLevel K n)).comp
        e.symm.toRingEquiv.toRingHom =
      (unramifiedLevelAlg
        k K e hnorm n).toRingHom.comp
        (algebraMap k (canonicalUnramifiedLevel k n)) := by
  apply RingHom.ext
  intro a
  simp only [RingHom.coe_comp, Function.comp_apply]
  change algebraMap K (canonicalUnramifiedLevel K n) (e.symm a) =
    unramifiedLevelAlg k K e hnorm n
      (algebraMap k (canonicalUnramifiedLevel k n) a)
  rw [level_alg_algebra]
  congr 1
  simpa using e.symm.commutes a

/-- The Galois equivalence induced by the canonical degree-`n` level
equivalence. -/
noncomputable def levelGalAlg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) [NeZero n] :
    Gal(canonicalUnramifiedLevel k n/k) ≃*
      Gal(canonicalUnramifiedLevel K n/K) :=
  galZeroUniverse e.symm.toRingEquiv
    (unramifiedLevelAlg k K e hnorm n)
    (level_alg_square
      k K e hnorm n)

/-- The canonical-level equivalence preserves the spectral norms defined
over the isometrically equivalent base fields. -/
theorem level_alg_spectral
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) [NeZero n]
    (x : canonicalUnramifiedLevel k n) :
    spectralNorm K (canonicalUnramifiedLevel K n)
        (unramifiedLevelAlg k K e hnorm n x) =
      spectralNorm k (canonicalUnramifiedLevel k n) x := by
  let U := canonicalUnramifiedLevel k n
  let V := canonicalUnramifiedLevel K n
  letI : Algebra K U :=
    levelTransportedAlgebra k K e n
  let g : U ≃ₐ[K] V :=
    canonicalLevelAlg k K e hnorm n
  have hbase (y : k) : e.symm y = algebraMap k K y := by
    apply e.injective
    simp
  have hsquare :
      (algebraMap K V).comp e.symm.toRingEquiv.toRingHom =
        g.toRingEquiv.toRingHom.comp (algebraMap k U) := by
    apply RingHom.ext
    intro y
    change algebraMap K V (e.symm y) = g (algebraMap k U y)
    rw [hbase]
    simpa [g, unramifiedLevelAlg] using
      (level_alg_algebra
        k K e hnorm n y).symm
  change spectralValue (minpoly K (g x)) = spectralValue (minpoly k x)
  have hmin := minpoly.map_eq_of_equiv_equiv
    (A := K) (R := k) (S := U) (T := V)
    (f := e.symm.toRingEquiv) (g := g.toRingEquiv) hsquare x
  calc
    spectralValue (minpoly K (g x)) =
        spectralValue ((minpoly k x).map e.symm.toRingEquiv.toRingHom) := by
          exact congrArg spectralValue hmin.symm
    _ = spectralValue (minpoly k x) :=
      spectral_value_norm
        e.symm.toRingEquiv hnorm (minpoly k x)

set_option maxHeartbeats 5000000 in
-- The residue-congruence extensionality proof installs both spectral local-field models.
set_option synthInstance.maxHeartbeats 500000 in
/-- The Galois equivalence induced by the canonical level equivalence sends
arithmetic Frobenius to arithmetic Frobenius. -/
theorem level_gal_frobenius
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) [NeZero n] :
    levelGalAlg k K e hnorm n
        (canonicalArithmeticFrobenius k n) =
      canonicalArithmeticFrobenius K n := by
  let U := canonicalUnramifiedLevel k n
  let V := canonicalUnramifiedLevel K n
  let i : U ≃+* V :=
    unramifiedLevelAlg k K e hnorm n
  let g : Gal(U/k) ≃* Gal(V/K) :=
    levelGalAlg k K e hnorm n
  letI : Algebra.IsAlgebraic k U := Algebra.IsAlgebraic.of_finite k U
  letI : NontriviallyNormedField U :=
    FLExt.nontriviallyNormedField k U
  letI : NormedAlgebra k U := spectralNorm.normedAlgebra k U
  letI : IsUltrametricDist U := IsUltrametricDist.of_normedAlgebra k
  letI : ValuativeRel U := FLExt.valuativeRel k U
  letI : Valuation.Compatible (NormedField.valuation (K := U)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := U))
  letI : IsNonarchimedeanLocalField U :=
    FLExt.nonarchimedeanLocalField k U
  letI : Algebra.IsAlgebraic K V := Algebra.IsAlgebraic.of_finite K V
  letI : NontriviallyNormedField V :=
    FLExt.nontriviallyNormedField K V
  letI : NormedAlgebra K V := spectralNorm.normedAlgebra K V
  letI : IsUltrametricDist V := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel V := FLExt.valuativeRel K V
  letI : Valuation.Compatible (NormedField.valuation (K := V)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := V))
  letI : IsNonarchimedeanLocalField V :=
    FLExt.nonarchimedeanLocalField K V
  have hiNorm (x : U) : ‖i x‖ = ‖x‖ := by
    change spectralNorm K V (i x) = spectralNorm k U x
    exact level_alg_spectral
      k K e hnorm n x
  have hcard : localResidueCardinality k = localResidueCardinality K := by
    exact local_residue_alg k K e hnorm
  change g (canonicalArithmeticFrobenius k n) =
    canonicalArithmeticFrobenius K n
  apply canonical_unramified_ext K n
  intro y hy
  let x : U := i.symm y
  have hx : ‖x‖ ≤ 1 := by
    rw [← hiNorm]
    simpa [x]
  have hsrc := subextension_arithmetic_frobenius
    k n x hx
  have htgt := subextension_arithmetic_frobenius
    K n y hy
  have hmapSrc :
      ‖i (canonicalArithmeticFrobenius k n x) -
          i (x ^ localResidueCardinality k)‖ < 1 := by
    rw [← map_sub, hiNorm]
    exact hsrc
  have hmapPow :
      i (x ^ localResidueCardinality k) =
        y ^ localResidueCardinality K := by
    rw [map_pow, hcard]
    simp [x]
  rw [hmapPow] at hmapSrc
  have htriangle := IsUltrametricDist.norm_add_le_max
    (g (canonicalArithmeticFrobenius k n) y -
      y ^ localResidueCardinality K)
    (y ^ localResidueCardinality K -
      canonicalArithmeticFrobenius K n y)
  have hgApply :
      g (canonicalArithmeticFrobenius k n) y =
        i (canonicalArithmeticFrobenius k n x) := by
    simpa [g, x] using gal_zero_universe
      e.symm.toRingEquiv i
      (level_alg_square
        k K e hnorm n)
      (canonicalArithmeticFrobenius k n) (i.symm y)
  have hadd :
      (g (canonicalArithmeticFrobenius k n) y -
          y ^ localResidueCardinality K) +
        (y ^ localResidueCardinality K -
          canonicalArithmeticFrobenius K n y) =
      g (canonicalArithmeticFrobenius k n) y -
        canonicalArithmeticFrobenius K n y := by ring
  rw [hadd] at htriangle
  exact htriangle.trans_lt (max_lt
    (by
      rw [hgApply]
      exact hmapSrc)
    (by
      rw [norm_sub_rev]
      exact htgt))

/-- The canonical level equivalence preserves every Frobenius-normalized
cyclic coordinate. -/
theorem level_gal_coordinate
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (n : ℕ) [NeZero n]
    (z : Multiplicative (ZMod n)) :
    levelGalAlg k K e hnorm n
        (levelZMod k n z) =
      levelZMod K n z := by
  let one : Multiplicative (ZMod n) := Multiplicative.ofAdd 1
  have hz : z ∈ Subgroup.zpowers one := by
    refine ⟨(z.toAdd.val : ℤ), ?_⟩
    change one ^ (z.toAdd.val : ℤ) = z
    rw [zpow_natCast]
    apply Multiplicative.toAdd.injective
    simp [one]
  obtain ⟨m, hm⟩ := hz
  rw [← hm]
  simp only [map_zpow]
  rw [level_frobenius_z,
    level_gal_frobenius,
    ← level_frobenius_z K n]

/-- The canonical equivalence at the factorial level used by the local
invariant construction. -/
noncomputable def factorialLevelAlg
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (r : ℕ) :
    unramifiedFactorialLevel k r ≃+*
      unramifiedFactorialLevel K r := by
  letI : NeZero (invariantLevelDegree r) :=
    ⟨(invariant_level_pos r).ne'⟩
  exact unramifiedLevelAlg k K e hnorm
    (invariantLevelDegree r)

/-- The factorial-level equivalence extends the original base-field
equivalence. -/
theorem factorial_level_algebra
    (e : K ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (r : ℕ) (a : k) :
    factorialLevelAlg k K e hnorm r
        (algebraMap k (unramifiedFactorialLevel k r) a) =
      algebraMap K (unramifiedFactorialLevel K r)
        (algebraMap k K a) := by
  letI : NeZero (invariantLevelDegree r) :=
    ⟨(invariant_level_pos r).ne'⟩
  exact level_alg_algebra
    k K e hnorm (invariantLevelDegree r) a

section ZeroUniverse

variable (k₀ : Type) (K₀ : Type u)
  [NontriviallyNormedField k₀] [IsUltrametricDist k₀] [ValuativeRel k₀]
  [IsNonarchimedeanLocalField k₀]
  [Valuation.Compatible (NormedField.valuation (K := k₀))]
  [NontriviallyNormedField K₀] [IsUltrametricDist K₀] [ValuativeRel K₀]
  [IsNonarchimedeanLocalField K₀]
  [Valuation.Compatible (NormedField.valuation (K := K₀))]
  [Algebra k₀ K₀] [FiniteDimensional k₀ K₀]

omit [FiniteDimensional k₀ K₀] in
/-- The induced factorial-level Galois equivalence preserves the canonical
Frobenius coordinate in the mixed-universe setting. -/
theorem factorial_level_coordinate
    (e : K₀ ≃ₐ[k₀] k₀)
    (hnorm : ∀ x : k₀, ‖e.symm x‖ = ‖x‖)
    (r : ℕ) [NeZero (invariantLevelDegree r)]
    (z : Multiplicative (ZMod (invariantLevelDegree r))) :
    factorialGalUniverse k₀ K₀ r e
        (factorialLevelAlg
          k₀ K₀ e hnorm r)
        (factorial_level_algebra
          k₀ K₀ e hnorm r)
        (factorialZMod k₀ r z) =
      factorialZMod K₀ r z := by
  simpa [factorialGalUniverse,
    levelGalAlg,
    factorialLevelAlg,
    factorialZMod] using
      (level_gal_coordinate
        k₀ K₀ e hnorm (invariantLevelDegree r) z)

omit [FiniteDimensional k₀ K₀] in
/-- An isometric field-model equivalence supplies the full mixed-universe
transport of the canonical factorial carry classes. -/
theorem factorial_universe_transport
    (e : K₀ ≃ₐ[k₀] k₀)
    (hnorm : ∀ x : k₀, ‖e.symm x‖ = ‖x‖) :
    FUTrans k₀ K₀ := by
  apply FUTrans.ring_equiv_fam
    k₀ K₀ e
    (factorialLevelAlg k₀ K₀ e hnorm)
    (factorial_level_algebra
      k₀ K₀ e hnorm)
  · intro r _ z
    exact
      factorial_level_coordinate
        k₀ K₀ e hnorm r z
  · have he : e.symm.toRingEquiv.toRingHom = algebraMap k₀ K₀ := by
      apply RingHom.ext
      intro x
      apply e.injective
      change e (e.symm x) = e (algebraMap k₀ K₀ x)
      rw [e.apply_symm_apply]
      exact (e.commutes x).symm
    rw [← he]
    exact mapped_uniformizer_alg k₀ K₀ e hnorm

omit [FiniteDimensional k₀ K₀] in
/-- Consequently, mixed-universe scalar extension along an isometric
field-model equivalence preserves the canonical local Brauer invariant. -/
theorem universe_preservation_alg
    (e : K₀ ≃ₐ[k₀] k₀)
    (hnorm : ∀ x : k₀, ‖e.symm x‖ = ‖x‖) :
    IUPreser k₀ K₀ :=
  IUPreser.canon_facto_carry
    k₀ K₀ e
    (factorial_universe_transport
      k₀ K₀ e hnorm)

end ZeroUniverse

end

end Towers.CField.LBrauer
