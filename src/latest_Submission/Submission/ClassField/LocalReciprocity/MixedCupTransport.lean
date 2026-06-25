import Submission.ClassField.LocalReciprocity.UniversePolymorphicArtin
import Submission.ClassField.LocalBrauer.CanonicalUniverseTransport
import Submission.ClassField.ReciprocityExistence.CupRestriction

/-!
# Character-cup transport across universes

This file transports the literal multiplicative character cup across
simultaneous equivalences of a Type-0 base field and finite Galois extension.
The crossed-product comparison is combined with the mixed-universe local
invariant preservation theorem.
-/

namespace Submission.CField.LRecip

open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer
open Submission.CField.RExist
open scoped IsMulCommutative TensorProduct

noncomputable section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Units.mulDistribMulActionRight

section Coefficients

variable {k L : Type} {F E : Type u}
  [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
  [Field F] [Algebra k F]
  [Field E] [Algebra F E] [Algebra k E] [IsScalarTower k F E]
  [FiniteDimensional F E]

/-- A compatible equivalence of finite extensions identifies the scalar
extension of the Type-0 source extension with the ambient target extension. -/
noncomputable def mixedUniverseAlg
    (i : L ≃+* E)
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (hdim : Module.finrank k L = Module.finrank F E) :
    L ⊗[k] F ≃ₐ[F] E := by
  let iAlg : L →ₐ[k] E :=
    { i.toRingHom with
      commutes' := by
        intro a
        change i (algebraMap k L a) = algebraMap k E a
        rw [hbase]
        exact (IsScalarTower.algebraMap_apply k F E a).symm }
  let fLeft : F ⊗[k] L →ₐ[F] E :=
    Algebra.TensorProduct.lift (Algebra.ofId F E) iAlg
      (fun _ _ => .all _ _)
  let f : L ⊗[k] F →ₐ[F] E :=
    fLeft.comp (Algebra.TensorProduct.commRight k F L).symm.toAlgHom
  letI : Module.Finite F (F ⊗[k] L) := Module.Finite.base_change k F L
  letI : Module.Finite F (L ⊗[k] F) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight k F L).toLinearEquiv
  have hdim' : Module.finrank F (L ⊗[k] F) = Module.finrank F E := by
    calc
      Module.finrank F (L ⊗[k] F) = Module.finrank F (F ⊗[k] L) :=
        (Algebra.TensorProduct.commRight k F L).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k L := Module.finrank_baseChange
        (R := F) (S := k) (M' := L)
      _ = Module.finrank F E := hdim
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := i.surjective y
    refine ⟨x ⊗ₜ[k] 1, ?_⟩
    simp [f, fLeft, iAlg]
  have hinj : Function.Injective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim' (f := f.toLinearMap)).2 hsurj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

@[simp]
theorem mixed_universe_tmul
    (i : L ≃+* E)
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (hdim : Module.finrank k L = Module.finrank F E)
    (a : L) (b : F) :
    mixedUniverseAlg i hbase hdim (a ⊗ₜ[k] b) =
      i a * algebraMap F E b := by
  simp [mixedUniverseAlg, mul_comm]

omit [FiniteDimensional k L] [Algebra k E] [IsScalarTower k F E]
  [FiniteDimensional F E] in
/-- The base and extension equivalences form a commuting square. -/
theorem mixed_universe_square
    (e : F ≃ₐ[k] k)
    (i : L ≃+* E)
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a)) :
    (algebraMap F E).comp e.symm.toRingEquiv.toRingHom =
      i.toRingHom.comp (algebraMap k L) := by
  apply RingHom.ext
  intro x
  change algebraMap F E (e.symm x) = i (algebraMap k L x)
  rw [hbase]
  congr 1
  apply e.injective
  change e (e.symm x) = e (algebraMap k F x)
  rw [e.apply_symm_apply]
  exact (e.commutes x).symm

/-- The Galois equivalence induced by a simultaneous equivalence of the
base and extension fields. -/
noncomputable def mixedUniverseGal
    (e : F ≃ₐ[k] k)
    (i : L ≃+* E)
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a)) :
    Gal(L/k) ≃* Gal(E/F) :=
  galZeroUniverse e.symm.toRingEquiv i
    (mixed_universe_square e i hbase)

end Coefficients

section Cup

variable (k L : Type) (F E : Type u)
  [NontriviallyNormedField k] [IsUltrametricDist k] [ValuativeRel k]
  [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  [NontriviallyNormedField F] [IsUltrametricDist F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]
  [Algebra k F] [FiniteDimensional k F]
  [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
  [Algebra k E] [IsScalarTower k F E]
  [IsMulCommutative Gal(L/k)] [IsMulCommutative Gal(E/F)]

set_option maxHeartbeats 4000000 in
-- Cocycle transport, tensor coefficients, and mixed local invariants elaborate together.
set_option synthInstance.maxHeartbeats 500000 in
omit [FiniteDimensional k F] in
/-- The ambient character-cup invariant is natural under simultaneous
equivalence of a Type-0 local base field and its finite Galois extension. -/
theorem ambient_cup_universe
    (e : F ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (i : L ≃+* E)
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a))
    (a : kˣ) (chi : CharacterModule (Additive Gal(E/F))) :
    let g := mixedUniverseGal e i hbase
    ambientCupInvariant k L a (chi.comp g.toAdditive) =
      ambientCupInvariant F E
        (Units.map (algebraMap k F).toMonoidHom a) chi := by
  have hsquare := mixed_universe_square e i hbase
  let g : Gal(L/k) ≃* Gal(E/F) :=
    mixedUniverseGal e i hbase
  have hi (sigma : Gal(L/k)) (x : L) :
      i (sigma x) = g sigma (i x) := by
    exact (gal_zero_universe
      e.symm.toRingEquiv i hsquare sigma x).symm
  let aF : Fˣ := Units.map (algebraMap k F).toMonoidHom a
  let cL : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ) :=
    invariantCupCocycle
      (Units.map (algebraMap k L).toMonoidHom a)
      (multiplicative_base_fixed k L a)
      (chi.comp g.toAdditive)
  let cE : NMCocycl₂ (G := Gal(E/F)) (M := Eˣ) :=
    invariantCupCocycle
      (Units.map (algebraMap F E).toMonoidHom aF)
      (multiplicative_base_fixed F E aF) chi
  have hc : transportedGaloisCocycle i.toRingHom g hi cL = cE := by
    apply NMCocycl₂.ext
    rintro ⟨sigma, tau⟩
    obtain ⟨sigma, rfl⟩ := g.surjective sigma
    obtain ⟨tau, rfl⟩ := g.surjective tau
    rw [transported_galois_cocycle]
    dsimp only [cL, cE, invariantCupCocycle]
    rw [map_zpow]
    have hexp : rationalBoundaryExponent
        (chi.comp g.toAdditive) sigma tau =
      rationalBoundaryExponent chi (g sigma) (g tau) := by
      simpa only using rational_boundary_comp
        g.toMonoidHom chi sigma tau
    rw [hexp]
    congr 1
    apply Units.ext
    exact hbase (a : k)
  have hdim : Module.finrank k L = Module.finrank F E := by
    exact Algebra.finrank_eq_of_equiv_equiv
      e.symm.toRingEquiv i hsquare
  let coeffEquiv : L ⊗[k] F ≃ₐ[F] E :=
    mixedUniverseAlg i hbase hdim
  have hbrauer := brauer_universe_crossed
    i.toRingHom g hi hbase cL coeffEquiv
      (mixed_universe_tmul i hbase hdim)
  rw [hc] at hbrauer
  have hinv := universe_preservation_alg
    k F e hnorm (CProduc.brauerClass k L cL)
  change (carryBrauerInvariant k
      (CProduc.brauerClass k L cL)).toAdd =
    (carryBrauerInvariant F
      (CProduc.brauerClass F E cE)).toAdd
  rw [← hbrauer]
  exact congrArg Multiplicative.toAdd hinv.symm

set_option maxHeartbeats 3000000 in
-- Character separation turns the mixed-universe cup comparison into
-- naturality of the universe-polymorphic finite local Artin map.
omit [FiniteDimensional k F] in
/-- The finite local Artin homomorphism is natural under simultaneous
isometric equivalences of the base local field and its finite Galois
extension. -/
theorem abelian_artin_universe
    (e : F ≃ₐ[k] k)
    (hnorm : ∀ x : k, ‖e.symm x‖ = ‖x‖)
    (i : L ≃+* E)
    (hbase : ∀ a : k,
      i (algebraMap k L a) = algebraMap F E (algebraMap k F a)) :
    let g := mixedUniverseGal e i hbase
    g.toMonoidHom.comp (abelianArtinUniverse k L) =
      (abelianArtinUniverse F E).comp
        (Units.map (algebraMap k F).toMonoidHom) := by
  dsimp only
  let g : Gal(L/k) ≃* Gal(E/F) :=
    mixedUniverseGal e i hbase
  apply MonoidHom.ext
  intro a
  apply forall_rational_character
  intro chi
  calc
    chi (Additive.ofMul
        (g (abelianArtinUniverse k L a))) =
        ambientCupInvariant k L a (chi.comp g.toAdditive) :=
      (abelian_universe_comp k L g.toMonoidHom a chi).symm
    _ = ambientCupInvariant F E
          (Units.map (algebraMap k F).toMonoidHom a) chi :=
      ambient_cup_universe
        k L F E e hnorm i hbase a chi
    _ = chi (Additive.ofMul
          (abelianArtinUniverse F E
            (Units.map (algebraMap k F).toMonoidHom a))) :=
      (abelian_universe_character F E
        (Units.map (algebraMap k F).toMonoidHom a) chi).symm

end Cup

end

end Submission.CField.LRecip
