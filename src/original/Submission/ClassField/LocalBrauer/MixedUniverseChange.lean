import Submission.ClassField.BrauerGroups.MixedUniverseChange
import Submission.ClassField.CrossedProducts.ProductBaseChange
import Submission.ClassField.LocalBrauer.InvariantBaseChange
import Submission.ClassField.LocalBrauer.InvariantBaseCarry

/-!
# Mixed-universe base change for the local Brauer invariant

This file isolates the local-invariant statement needed when a Type-0 model
of a local field is transported to an ambient universe.  The scalar-extension
map itself is `brauerChangeUniverse`; the remaining arithmetic input
is its compatibility with the canonical local Brauer invariant.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u v

open ValuativeRel
open BGroups
open CProduca
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Units.mulDistribMulActionRight

variable (k : Type) (K : Type u)
  [NontriviallyNormedField k] [IsUltrametricDist k] [ValuativeRel k]
  [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Algebra k K] [FiniteDimensional k K]

/-- The local-invariant restriction formula for scalar extension from a
Type-0 local field to a local field in an arbitrary universe. -/
def CUForm : Prop :=
  ∀ x : BrauerGroup.{0, 0} k,
    carryBrauerInvariant K
        (brauerChangeUniverse k K x) =
      (carryBrauerInvariant k x) ^ Module.finrank k K

/-- For a degree-one change of universe, the mixed base-change formula says
exactly that the canonical local invariant is preserved. -/
def IUPreser : Prop :=
  ∀ x : BrauerGroup.{0, 0} k,
    carryBrauerInvariant K
        (brauerChangeUniverse k K x) =
      carryBrauerInvariant k x

/-- The concrete field-theoretic transport statement at the canonical
factorial levels: scalar extension carries the source carry crossed product
to the target carry crossed product at the same level. -/
def FUTrans : Prop :=
  ∀ r : ℕ,
    brauerChangeUniverse k K
        (((FIData.carry k
            (factorialZMod k) r :
          brauerCofinalLevel k
            (unramifiedFactorialLevel k) r) :
          BrauerGroup k)) =
      (((FIData.carry K
          (factorialZMod K) r :
        brauerCofinalLevel K
          (unramifiedFactorialLevel K) r) :
        BrauerGroup K))

omit [IsUltrametricDist k] [ValuativeRel k]
  [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [FiniteDimensional k K] in
/-- A `k`-algebra equivalence with the base field forces the mixed extension
to have degree one. -/
theorem finrank_alg_universe
    (e : K ≃ₐ[k] k) : Module.finrank k K = 1 := by
  rw [e.toLinearEquiv.finrank_eq]
  exact Module.finrank_self k

omit [FiniteDimensional k K] in
/-- Along a field-model equivalence, the degree formula and preservation of
the canonical invariant are equivalent formulations. -/
theorem change_universe_preservation
    (e : K ≃ₐ[k] k) :
    CUForm k K ↔
      IUPreser k K := by
  rw [CUForm,
    IUPreser,
    finrank_alg_universe k K e]
  simp

set_option maxHeartbeats 1000000 in
-- Unfolding the dependent factorial tower in the cofinality witness is deep.
omit [FiniteDimensional k K] in
/-- It suffices to verify the mixed-universe base-change formula on the carry
generator at every canonical factorial level. -/
theorem CUForm.canon_factorial_carry
    (hcarry : ∀ r : ℕ,
      carryBrauerInvariant K
          (brauerChangeUniverse k K
            (((FIData.carry k
                (factorialZMod k) r :
              brauerCofinalLevel k
                (unramifiedFactorialLevel k) r) :
              BrauerGroup k))) =
        (carryBrauerInvariant k
          (((FIData.carry k
              (factorialZMod k) r :
            brauerCofinalLevel k
              (unramifiedFactorialLevel k) r) :
            BrauerGroup k))) ^ Module.finrank k K) :
    CUForm k K := by
  intro x
  obtain ⟨r, hx⟩ := factorialBrauerCofinal k x
  let y : brauerCofinalLevel k
      (unramifiedFactorialLevel k) r := ⟨x, hx⟩
  obtain ⟨i, hi⟩ :=
    FIData.carry_pow k
      (factorialInvariantData k)
      (factorialZMod k) r y
  let c : BrauerGroup k :=
    ((FIData.carry k
        (factorialZMod k) r :
      brauerCofinalLevel k (unramifiedFactorialLevel k) r) :
        BrauerGroup k)
  have hxpow : x = c ^ i := by
    change y.1 = c ^ i
    exact congrArg Subtype.val hi
  rw [hxpow, map_pow, map_pow, hcarry r, map_pow, ← pow_mul, ← pow_mul,
    Nat.mul_comm]

omit [FiniteDimensional k K] in
/-- For a field-model equivalence, preservation on the canonical factorial
carry classes already implies preservation on the entire Brauer group. -/
theorem IUPreser.canon_factorial_carry
    (e : K ≃ₐ[k] k)
    (hcarry : ∀ r : ℕ,
      carryBrauerInvariant K
          (brauerChangeUniverse k K
            (((FIData.carry k
                (factorialZMod k) r :
              brauerCofinalLevel k
                (unramifiedFactorialLevel k) r) :
              BrauerGroup k))) =
        carryBrauerInvariant k
          (((FIData.carry k
              (factorialZMod k) r :
            brauerCofinalLevel k
              (unramifiedFactorialLevel k) r) :
            BrauerGroup k))) :
    IUPreser k K := by
  rw [← change_universe_preservation
    k K e]
  apply CUForm.canon_factorial_carry
  intro r
  rw [finrank_alg_universe k K e, pow_one]
  exact hcarry r

omit [FiniteDimensional k K] in
/-- Identifying the scalar-extended carry crossed products with the target
canonical carries proves preservation of the entire local invariant. -/
theorem IUPreser.canon_facto_carry
    (e : K ≃ₐ[k] k)
    (htransport : FUTrans k K) :
    IUPreser k K := by
  apply IUPreser.canon_factorial_carry
    k K e
  intro r
  rw [htransport r, carry_brauer_invariant,
    carry_brauer_invariant]

/-- Conjugating both fields in an extension square transports a Galois
automorphism across universes. -/
noncomputable def transportGalUniverse
    {F L : Type v} {K E : Type u}
    [Field F] [Field L] [Field K] [Field E]
    [Algebra F L] [Algebra K E]
    (f : F ≃+* K) (i : L ≃+* E)
    (h : (algebraMap K E).comp f.toRingHom =
      i.toRingHom.comp (algebraMap F L))
    (sigma : Gal(L/F)) : Gal(E/K) := by
  let c : E ≃+* E := i.symm.trans (sigma.toRingEquiv.trans i)
  exact AlgEquiv.ofRingEquiv (f := c) fun x => by
    change i (sigma (i.symm (algebraMap K E x))) = algebraMap K E x
    have hsquare := DFunLike.congr_fun h (f.symm x)
    have hpreimage : i.symm (algebraMap K E x) =
        algebraMap F L (f.symm x) := by
      apply i.injective
      rw [i.apply_symm_apply]
      simpa using hsquare
    rw [hpreimage, sigma.commutes]
    simpa using hsquare.symm

@[simp]
theorem transport_gal_universe
    {F L : Type v} {K E : Type u}
    [Field F] [Field L] [Field K] [Field E]
    [Algebra F L] [Algebra K E]
    (f : F ≃+* K) (i : L ≃+* E)
    (h : (algebraMap K E).comp f.toRingHom =
      i.toRingHom.comp (algebraMap F L))
    (sigma : Gal(L/F)) (x : E) :
    transportGalUniverse f i h sigma x =
      i (sigma (i.symm x)) := by
  rfl

/-- The Galois groups in a commutative square of field equivalences are
multiplicatively equivalent, in possibly different universes. -/
noncomputable def galZeroUniverse
    {F L : Type v} {K E : Type u}
    [Field F] [Field L] [Field K] [Field E]
    [Algebra F L] [Algebra K E]
    (f : F ≃+* K) (i : L ≃+* E)
    (h : (algebraMap K E).comp f.toRingHom =
      i.toRingHom.comp (algebraMap F L)) :
    Gal(L/F) ≃* Gal(E/K) := by
  have hInv : (algebraMap F L).comp f.symm.toRingHom =
      i.symm.toRingHom.comp (algebraMap K E) := by
    apply RingHom.ext
    intro x
    apply i.injective
    simpa using (DFunLike.congr_fun h (f.symm x)).symm
  exact
    { toFun := transportGalUniverse f i h
      invFun := transportGalUniverse f.symm i.symm hInv
      left_inv := by
        intro sigma
        ext x
        rw [transport_gal_universe,
          transport_gal_universe]
        simp
      right_inv := by
        intro sigma
        ext x
        rw [transport_gal_universe,
          transport_gal_universe]
        simp
      map_mul' := by
        intro sigma tau
        ext x
        change i ((sigma * tau) (i.symm x)) =
          i (sigma (i.symm (i (tau (i.symm x)))))
        simp }

@[simp]
theorem gal_zero_universe
    {F L : Type v} {K E : Type u}
    [Field F] [Field L] [Field K] [Field E]
    [Algebra F L] [Algebra K E]
    (f : F ≃+* K) (i : L ≃+* E)
    (h : (algebraMap K E).comp f.toRingHom =
      i.toRingHom.comp (algebraMap F L))
    (sigma : Gal(L/F)) (x : L) :
    galZeroUniverse f i h sigma (i x) = i (sigma x) := by
  rw [show galZeroUniverse f i h sigma =
      transportGalUniverse f i h sigma by rfl,
    transport_gal_universe, i.symm_apply_apply]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [FiniteDimensional k K] in
/-- The base and level equivalences used for factorial carry transport form
a commutative square of field homomorphisms. -/
theorem factorial_level_square
    (r : ℕ)
    (e : K ≃ₐ[k] k)
    (i : unramifiedFactorialLevel k r ≃+*
      unramifiedFactorialLevel K r)
    (hbase : ∀ a : k,
      i (algebraMap k (unramifiedFactorialLevel k r) a) =
        algebraMap K (unramifiedFactorialLevel K r)
          (algebraMap k K a)) :
    (algebraMap K (unramifiedFactorialLevel K r)).comp
        e.symm.toRingEquiv.toRingHom =
      i.toRingHom.comp
        (algebraMap k (unramifiedFactorialLevel k r)) := by
  apply RingHom.ext
  intro a
  change algebraMap K (unramifiedFactorialLevel K r) (e.symm a) =
    i (algebraMap k (unramifiedFactorialLevel k r) a)
  rw [hbase]
  congr 1
  simpa using e.symm.commutes a

/-- The Galois equivalence canonically induced by compatible base and
factorial-level field equivalences. -/
noncomputable def factorialGalUniverse
    (r : ℕ)
    (e : K ≃ₐ[k] k)
    (i : unramifiedFactorialLevel k r ≃+*
      unramifiedFactorialLevel K r)
    (hbase : ∀ a : k,
      i (algebraMap k (unramifiedFactorialLevel k r) a) =
        algebraMap K (unramifiedFactorialLevel K r)
          (algebraMap k K a)) :
    Gal(unramifiedFactorialLevel k r/k) ≃*
      Gal(unramifiedFactorialLevel K r/K) :=
  galZeroUniverse e.symm.toRingEquiv i
    (factorial_level_square k K r e i hbase)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k]
  [Valuation.Compatible (NormedField.valuation (K := k))]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [FiniteDimensional k K] in
@[simp]
theorem factorial_gal_universe
    (r : ℕ)
    (e : K ≃ₐ[k] k)
    (i : unramifiedFactorialLevel k r ≃+*
      unramifiedFactorialLevel K r)
    (hbase : ∀ a : k,
      i (algebraMap k (unramifiedFactorialLevel k r) a) =
        algebraMap K (unramifiedFactorialLevel K r)
          (algebraMap k K a))
    (sigma : Gal(unramifiedFactorialLevel k r/k))
    (x : unramifiedFactorialLevel k r) :
    factorialGalUniverse k K r e i hbase sigma (i x) =
      i (sigma x) :=
  gal_zero_universe e.symm.toRingEquiv i
    (factorial_level_square k K r e i hbase) sigma x

/-- Transporting a carry cocycle through coefficient and cyclic Galois
coordinates works unchanged when the source and target fields inhabit
different universes. -/
theorem transported_cocycle_universe
    {F U : Type v} {K E : Type u}
    [Field F] [Field U] [Field K] [Field E]
    [Algebra F U] [FiniteDimensional F U] [IsGalois F U]
    [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    [Algebra F K] [Algebra F E] [IsScalarTower F K E]
    {n : ℕ} [NeZero n]
    (i : U →+* E) (g : Gal(U/F) ≃* Gal(E/K))
    (hi : ∀ sigma : Gal(U/F), ∀ a : U,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : F,
      i (algebraMap F U a) = algebraMap K E (algebraMap F K a))
    (eF : Multiplicative (ZMod n) ≃* Gal(U/F))
    (eK : Multiplicative (ZMod n) ≃* Gal(E/K))
    (hcoord : ∀ z, g (eF z) = eK z)
    (a : Fˣ) :
    transportedGaloisCocycle i g hi (galoisCarryCocycle F eF a) =
      galoisCarryCocycle K eK (Units.map (algebraMap F K) a) := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Uˣ :=
    GroupH2.pulledAction eF
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Eˣ :=
    GroupH2.pulledAction eK
  apply NMCocycl₂.ext
  rintro ⟨sigma, tau⟩
  let sigmaF : Gal(U/F) := g.symm sigma
  let tauF : Gal(U/F) := g.symm tau
  have hsigma : sigma = g sigmaF := by simp [sigmaF]
  have htau : tau = g tauF := by simp [tauF]
  rw [hsigma, htau, transported_galois_cocycle]
  dsimp only [galoisCarryCocycle]
  rw [MHTrans.cocycleMap_apply,
    MHTrans.cocycleMap_apply]
  have hsigmaCoord : eK.symm (g sigmaF) = eF.symm sigmaF := by
    apply eK.injective
    rw [eK.apply_symm_apply, ← hcoord, eF.apply_symm_apply]
  have htauCoord : eK.symm (g tauF) = eF.symm tauF := by
    apply eK.injective
    rw [eK.apply_symm_apply, ← hcoord, eF.apply_symm_apply]
  rw [hsigmaCoord, htauCoord]
  change Units.map i
      ((Units.map (algebraMap F U).toMonoidHom a) ^
        CCarry.carry (eF.symm sigmaF).toAdd (eF.symm tauF).toAdd) =
    (Units.map (algebraMap K E).toMonoidHom
      (Units.map (algebraMap F K).toMonoidHom a)) ^
      CCarry.carry (eF.symm sigmaF).toAdd (eF.symm tauF).toAdd
  rw [map_pow]
  apply congrArg (fun x : Eˣ ↦ x ^
    CCarry.carry (eF.symm sigmaF).toAdd (eF.symm tauF).toAdd)
  apply Units.ext
  exact hbase a

set_option maxHeartbeats 1000000 in
-- Tensor base change and the two dependent canonical levels elaborate together.
set_option synthInstance.maxHeartbeats 200000 in
/-- A compatible ring equivalence between two canonical factorial levels
identifies the scalar extension of the source level with the target level. -/
noncomputable def canonicalFactorialAlg
    (r : ℕ)
    [NeZero (invariantLevelDegree r)]
    [Algebra k (unramifiedFactorialLevel K r)]
    [IsScalarTower k K (unramifiedFactorialLevel K r)]
    (i : unramifiedFactorialLevel k r ≃+*
      unramifiedFactorialLevel K r)
    (hbase : ∀ a : k,
      i (algebraMap k (unramifiedFactorialLevel k r) a) =
        algebraMap K (unramifiedFactorialLevel K r)
          (algebraMap k K a)) :
    unramifiedFactorialLevel k r ⊗[k] K ≃ₐ[K]
      unramifiedFactorialLevel K r := by
  let iAlg : unramifiedFactorialLevel k r →ₐ[k]
      unramifiedFactorialLevel K r :=
    { i.toRingHom with
      commutes' := by
        intro a
        change i (algebraMap k (unramifiedFactorialLevel k r) a) =
          algebraMap k (unramifiedFactorialLevel K r) a
        rw [hbase]
        exact (IsScalarTower.algebraMap_apply k K
          (unramifiedFactorialLevel K r) a).symm }
  let fLeft : K ⊗[k] unramifiedFactorialLevel k r →ₐ[K]
      unramifiedFactorialLevel K r :=
    Algebra.TensorProduct.lift
      (Algebra.ofId K (unramifiedFactorialLevel K r)) iAlg
      (fun _ _ ↦ .all _ _)
  let f : unramifiedFactorialLevel k r ⊗[k] K →ₐ[K]
      unramifiedFactorialLevel K r :=
    fLeft.comp (Algebra.TensorProduct.commRight k K
      (unramifiedFactorialLevel k r)).symm.toAlgHom
  letI : Module.Finite K
      (K ⊗[k] unramifiedFactorialLevel k r) :=
    Module.Finite.base_change k K (unramifiedFactorialLevel k r)
  letI : Module.Finite K
      (unramifiedFactorialLevel k r ⊗[k] K) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight k K
        (unramifiedFactorialLevel k r)).toLinearEquiv
  have hdim : Module.finrank K
      (unramifiedFactorialLevel k r ⊗[k] K) =
      Module.finrank K (unramifiedFactorialLevel K r) := by
    calc
      Module.finrank K
          (unramifiedFactorialLevel k r ⊗[k] K) =
          Module.finrank K
            (K ⊗[k] unramifiedFactorialLevel k r) :=
        (Algebra.TensorProduct.commRight k K
          (unramifiedFactorialLevel k r)).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank k (unramifiedFactorialLevel k r) :=
        Module.finrank_baseChange (R := K) (S := k)
          (M' := unramifiedFactorialLevel k r)
      _ = invariantLevelDegree r :=
        factorial_level_finrank k r
      _ = Module.finrank K (unramifiedFactorialLevel K r) :=
        (factorial_level_finrank K r).symm
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := i.surjective y
    refine ⟨x ⊗ₜ[k] 1, ?_⟩
    simp [f, fLeft, iAlg]
  have hinj : Function.Injective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hdim (f := f.toLinearMap)).2 hsurj
  exact AlgEquiv.ofBijective f ⟨hinj, hsurj⟩

set_option maxHeartbeats 1000000 in
-- Unfolding the bijective tensor lift exposes both canonical-level structures.
omit [FiniteDimensional k K] in
@[simp]
theorem canonical_factorial_tmul
    (r : ℕ)
    [NeZero (invariantLevelDegree r)]
    [Algebra k (unramifiedFactorialLevel K r)]
    [IsScalarTower k K (unramifiedFactorialLevel K r)]
    (i : unramifiedFactorialLevel k r ≃+*
      unramifiedFactorialLevel K r)
    (hbase : ∀ a : k,
      i (algebraMap k (unramifiedFactorialLevel k r) a) =
        algebraMap K (unramifiedFactorialLevel K r)
          (algebraMap k K a))
    (a : unramifiedFactorialLevel k r) (b : K) :
    canonicalFactorialAlg k K r i hbase (a ⊗ₜ[k] b) =
      i a * algebraMap K (unramifiedFactorialLevel K r) b := by
  simp [canonicalFactorialAlg, mul_comm]

set_option maxHeartbeats 3000000 in
-- This wrapper caches the dependent local-field telescope of the carry comparison.
set_option synthInstance.maxHeartbeats 600000 in
/-- An order-one parameter in the target canonical unramified level gives
the target canonical factorial carry, in the exact absolute-Brauer form used
by mixed scalar extension. -/
theorem factorial_carry_brauer
    (r : ℕ) [NeZero (invariantLevelDegree r)]
    (u : Kˣ) (horder :
      localUnitOrder K (Additive.ofMul u) = 1) :
    CProduc.brauerClass K (unramifiedFactorialLevel K r)
        (galoisCarryCocycle K
          (factorialZMod K r) u) =
      (((FIData.carry K
          (factorialZMod K) r :
        brauerCofinalLevel K
          (unramifiedFactorialLevel K) r) :
        BrauerGroup K)) := by
  exact carry_brauer_factorial
    K r u horder

set_option maxHeartbeats 3000000 in
-- The mixed tensor coefficient equivalence and both dependent carries elaborate together.
set_option synthInstance.maxHeartbeats 600000 in
omit [FiniteDimensional k K] in
/-- The finite-level crossed-product calculation behind
`FUTrans`.  Once the source and target
unramified levels, Frobenius coordinates, and coefficients have been
identified, the mixed Brauer scalar-extension theorem proves the desired
carry-class equality. -/
theorem carry_universe_transport
    (r : ℕ)
    [NeZero (invariantLevelDegree r)]
    [Algebra k (unramifiedFactorialLevel K r)]
    [IsScalarTower k K (unramifiedFactorialLevel K r)]
    (i : unramifiedFactorialLevel k r ≃+*
      unramifiedFactorialLevel K r)
    (g : Gal(unramifiedFactorialLevel k r/k) ≃*
      Gal(unramifiedFactorialLevel K r/K))
    (hi : ∀ sigma : Gal(unramifiedFactorialLevel k r/k),
      ∀ a : unramifiedFactorialLevel k r,
        i (sigma a) = g sigma (i a))
    (hbase : ∀ a : k,
      i (algebraMap k (unramifiedFactorialLevel k r) a) =
        algebraMap K (unramifiedFactorialLevel K r) (algebraMap k K a))
    (hcoord : ∀ z,
      g (factorialZMod k r z) =
        factorialZMod K r z)
    (horder : localUnitOrder K
      (Additive.ofMul
        (Units.map (algebraMap k K) (canonicalLocalUniformizer k))) = 1) :
    brauerChangeUniverse k K
        (((FIData.carry k
            (factorialZMod k) r :
          brauerCofinalLevel k
            (unramifiedFactorialLevel k) r) :
          BrauerGroup k)) =
      (((FIData.carry K
          (factorialZMod K) r :
        brauerCofinalLevel K
          (unramifiedFactorialLevel K) r) :
        BrauerGroup K)) := by
  change brauerChangeUniverse k K
      (CProduc.brauerClass k (unramifiedFactorialLevel k r)
        (galoisCarryCocycle k
          (factorialZMod k r)
          (canonicalLocalUniformizer k))) = _
  let u : Kˣ := Units.map (algebraMap k K) (canonicalLocalUniformizer k)
  have horderU : localUnitOrder K (Additive.ofMul u) = 1 := horder
  let coeffEquiv := canonicalFactorialAlg k K r i hbase
  rw [brauer_universe_crossed
    i.toRingHom g hi hbase _ coeffEquiv
      (canonical_factorial_tmul k K r i hbase)]
  rw [transported_cocycle_universe
    i.toRingHom g hi hbase
      (factorialZMod k r)
      (factorialZMod K r) hcoord
      (canonicalLocalUniformizer k)]
  change CProduc.brauerClass K
      (unramifiedFactorialLevel K r)
      (galoisCarryCocycle K
        (factorialZMod K r) u) = _
  exact factorial_carry_brauer K r u horderU

set_option maxHeartbeats 3000000 in
-- The canonical Galois conjugation, tensor lift, and carry comparison elaborate together.
set_option synthInstance.maxHeartbeats 600000 in
omit [FiniteDimensional k K] in
/-- At one factorial level, a compatible field equivalence preserving the
Frobenius coordinate and normalized order transports the canonical carry. -/
theorem factorial_carry_universe
    (r : ℕ)
    [NeZero (invariantLevelDegree r)]
    [Algebra k (unramifiedFactorialLevel K r)]
    [IsScalarTower k K (unramifiedFactorialLevel K r)]
    (e : K ≃ₐ[k] k)
    (i : unramifiedFactorialLevel k r ≃+*
      unramifiedFactorialLevel K r)
    (hbase : ∀ a : k,
      i (algebraMap k (unramifiedFactorialLevel k r) a) =
        algebraMap K (unramifiedFactorialLevel K r)
          (algebraMap k K a))
    (hcoord : ∀ z,
      factorialGalUniverse k K r e i hbase
          (factorialZMod k r z) =
        factorialZMod K r z)
    (horder : localUnitOrder K
      (Additive.ofMul
        (Units.map (algebraMap k K) (canonicalLocalUniformizer k))) = 1) :
    brauerChangeUniverse k K
        (((FIData.carry k
            (factorialZMod k) r :
          brauerCofinalLevel k
            (unramifiedFactorialLevel k) r) :
          BrauerGroup k)) =
      (((FIData.carry K
          (factorialZMod K) r :
        brauerCofinalLevel K
          (unramifiedFactorialLevel K) r) :
        BrauerGroup K)) := by
  let g := factorialGalUniverse k K r e i hbase
  apply carry_universe_transport k K r i g
  · intro sigma a
    exact (factorial_gal_universe
      k K r e i hbase sigma a).symm
  · exact hbase
  · exact hcoord
  · exact horder

omit [FiniteDimensional k K] in
/-- A compatible family of factorial-level field equivalences preserving
Frobenius, together with preservation of normalized order on the base
uniformizer, proves the full canonical carry transport statement. -/
theorem FUTrans.ring_equiv_fam
    (e : K ≃ₐ[k] k)
    (i : ∀ r : ℕ,
      unramifiedFactorialLevel k r ≃+*
        unramifiedFactorialLevel K r)
    (hbase : ∀ (r : ℕ) (a : k),
      i r (algebraMap k (unramifiedFactorialLevel k r) a) =
        algebraMap K (unramifiedFactorialLevel K r)
          (algebraMap k K a))
    (hcoord : ∀ (r : ℕ) [NeZero (invariantLevelDegree r)] z,
      factorialGalUniverse k K r e (i r) (hbase r)
          (factorialZMod k r z) =
        factorialZMod K r z)
    (horder : localUnitOrder K
      (Additive.ofMul
        (Units.map (algebraMap k K) (canonicalLocalUniformizer k))) = 1) :
    FUTrans k K := by
  intro r
  letI : NeZero (invariantLevelDegree r) :=
    ⟨(invariant_level_pos r).ne'⟩
  exact factorial_carry_universe
    k K r e (i r) (hbase r) (hcoord r) horder

end

end Submission.CField.LBrauer
