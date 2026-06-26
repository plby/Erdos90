import Towers.ClassField.CrossedProducts.ProductBaseChange
import Towers.ClassField.LocalBrauer.ConcreteInflationComparison
import Towers.ClassField.LocalBrauer.FieldAdicOrder
import Towers.ClassField.LocalBrauer.UnramifiedFiniteInvariant
import Towers.NumberTheory.Locals.TotallyRamifiedEisenstein

/-!
# Base change of an unramified carry class

This file isolates the algebraic calculation needed for base change along a
field linearly disjoint from a cyclic unramified extension.  The hypotheses
are phrased in terms of the tensor-compositum data produced by linear
disjointness: an embedding of the old coefficient field, the induced Galois
equivalence, and the tensor-product equivalence onto the compositum.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups CProduca
open scoped TensorProduct

attribute [local instance] Units.mulDistribMulActionRight
attribute [local instance] Algebra.TensorProduct.rightAlgebra

section GaloisCarry

variable {K U F E : Type u}
  [Field K] [Field U] [Field F] [Field E]
  [Algebra K U] [FiniteDimensional K U] [IsGalois K U]
  [Algebra K F] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
  [Algebra K E] [IsScalarTower K F E]

variable {n : ℕ} [NeZero n]

omit [FiniteDimensional K U] [IsGalois K U]
  [FiniteDimensional F E] [IsGalois F E]
  [Algebra K E] [IsScalarTower K F E] in
/-- Transporting a carry cocycle through compatible coefficient and cyclic
Galois coordinates gives the carry cocycle of the base-changed extension. -/
theorem transported_cocycle_carry
    (i : U →+* E) (g : Gal(U/K) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(U/K), ∀ a : U,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : K,
      i (algebraMap K U a) = algebraMap F E (algebraMap K F a))
    (eK : Multiplicative (ZMod n) ≃* Gal(U/K))
    (eF : Multiplicative (ZMod n) ≃* Gal(E/F))
    (hcoord : ∀ z, g (eK z) = eF z)
    (a : Kˣ) :
    transportedGaloisCocycle i g hi (galoisCarryCocycle K eK a) =
      galoisCarryCocycle F eF (Units.map (algebraMap K F) a) := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Uˣ :=
    GroupH2.pulledAction eK
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Eˣ :=
    GroupH2.pulledAction eF
  apply NMCocycl₂.ext
  rintro ⟨sigma, tau⟩
  let sigmaK : Gal(U/K) := g.symm sigma
  let tauK : Gal(U/K) := g.symm tau
  have hsigma : sigma = g sigmaK := by
    simp [sigmaK]
  have htau : tau = g tauK := by
    simp [tauK]
  rw [hsigma, htau]
  rw [transported_galois_cocycle]
  dsimp only [galoisCarryCocycle]
  rw [MHTrans.cocycleMap_apply,
    MHTrans.cocycleMap_apply]
  have hsigmaCoord : eF.symm (g sigmaK) = eK.symm sigmaK := by
    apply eF.injective
    rw [eF.apply_symm_apply, ← hcoord, eK.apply_symm_apply]
  have htauCoord : eF.symm (g tauK) = eK.symm tauK := by
    apply eF.injective
    rw [eF.apply_symm_apply, ← hcoord, eK.apply_symm_apply]
  rw [hsigmaCoord, htauCoord]
  change Units.map i
      ((Units.map (algebraMap K U).toMonoidHom a) ^
        CCarry.carry (eK.symm sigmaK).toAdd (eK.symm tauK).toAdd) =
    (Units.map (algebraMap F E).toMonoidHom
      (Units.map (algebraMap K F).toMonoidHom a)) ^
      CCarry.carry (eK.symm sigmaK).toAdd (eK.symm tauK).toAdd
  rw [map_pow]
  apply congrArg (fun x : Eˣ ↦ x ^
    CCarry.carry (eK.symm sigmaK).toAdd (eK.symm tauK).toAdd)
  apply Units.ext
  exact hbase a

omit [Algebra K E] [IsScalarTower K F E] in
/-- Under tensor-compositum data and compatible cyclic coordinates, scalar
extension sends a carry crossed-product Brauer class to the corresponding
carry crossed-product class over the new base field. -/
theorem brauer_base_carry
    (i : U →+* E) (g : Gal(U/K) ≃* Gal(E/F))
    (hi : ∀ sigma : Gal(U/K), ∀ a : U,
      i (sigma a) = g sigma (i a))
    (hbase : ∀ a : K,
      i (algebraMap K U a) = algebraMap F E (algebraMap K F a))
    (coeffEquiv : U ⊗[K] F ≃ₐ[F] E)
    (hcoeff : ∀ (a : U) (b : F),
      coeffEquiv (a ⊗ₜ[K] b) = i a * algebraMap F E b)
    (eK : Multiplicative (ZMod n) ≃* Gal(U/K))
    (eF : Multiplicative (ZMod n) ≃* Gal(E/F))
    (hcoord : ∀ z, g (eK z) = eF z)
    (a : Kˣ) :
    brauerBaseChange K F
        (CProduc.brauerClass K U (galoisCarryCocycle K eK a)) =
      CProduc.brauerClass F E
        (galoisCarryCocycle F eF (Units.map (algebraMap K F) a)) := by
  rw [brauer_base_crossed i g hi hbase
    (galoisCarryCocycle K eK a) coeffEquiv hcoeff]
  rw [transported_cocycle_carry
    i g hi hbase eK eF hcoord a]

end GaloisCarry

section FiniteInvariant

variable (K U F E : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField U] [IsUltrametricDist U] [ValuativeRel U]
  [IsNonarchimedeanLocalField U]
  [Valuation.Compatible (NormedField.valuation (K := U))]
  [NontriviallyNormedField F] [IsUltrametricDist F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]
  [Valuation.Compatible (NormedField.valuation (K := F))]
  [NontriviallyNormedField E] [IsUltrametricDist E] [ValuativeRel E]
  [IsNonarchimedeanLocalField E]
  [Valuation.Compatible (NormedField.valuation (K := E))]
  [Algebra K U] [Module.Finite K U] [IsGalois K U]
  [Algebra F E] [Module.Finite F E] [IsGalois F E]
  [Algebra K F]
  [Algebra 𝓀[K] 𝓀[U]] [Algebra 𝓀[F] 𝓀[E]]

variable {n : ℕ} [NeZero n]

/-- If normalized order scales by `d` under `K → F`, then the finite
unramified invariant of the carry class with base-changed parameter is the
`d`-th power of the original finite invariant. -/
theorem unramified_invariant_carry
    (eK : Multiplicative (ZMod n) ≃* Gal(U/K))
    (eF : Multiplicative (ZMod n) ≃* Gal(E/F))
    (hn : 1 < n)
    (NK : 𝒪[U]ˣ →* 𝒪[K]ˣ) (hNK : UnramifiedLocalData K U NK)
    (horderNormK : ∀ x : Uˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K U x)) =
        (n : ℤ) * localUnitOrder U (Additive.ofMul x))
    (NF : 𝒪[E]ˣ →* 𝒪[F]ˣ) (hNF : UnramifiedLocalData F E NF)
    (horderNormF : ∀ x : Eˣ,
      localUnitOrder F
          (Additive.ofMul (localNormUnits F E x)) =
        (n : ℤ) * localUnitOrder E (Additive.ofMul x))
    (d : ℕ) (a : Kˣ)
    (horder : localUnitOrder F
        (Additive.ofMul (Units.map (algebraMap K F) a)) =
      (d : ℤ) * localUnitOrder K (Additive.ofMul a)) :
    unramifiedInvariantEquiv F E eF hn NF hNF horderNormF
        (unramifiedCarryRelative F E eF
          (Units.map (algebraMap K F) a)) =
      (unramifiedInvariantEquiv K U eK hn NK hNK horderNormK
        (unramifiedCarryRelative K U eK a)) ^ d := by
  rw [unramified_mul_carry,
    unramified_mul_carry]
  apply Multiplicative.toAdd.injective
  change torsionZMod n
      (localUnitOrder F
        (Additive.ofMul (Units.map (algebraMap K F) a)) : ZMod n) =
    d • torsionZMod n
      (localUnitOrder K (Additive.ofMul a) : ZMod n)
  rw [← map_nsmul]
  apply congrArg (torsionZMod n)
  rw [horder]
  simp [nsmul_eq_mul]

/-- Integer-ring ramification supplies the order-scaling hypothesis in the
preceding theorem.  Thus the transported carry invariant is raised precisely
to the ramification index. -/
theorem carry_ramification_idx
    [Algebra 𝒪[K] 𝒪[F]] [Module.IsTorsionFree 𝒪[K] 𝒪[F]]
    [IsScalarTower 𝒪[K] K F] [IsScalarTower 𝒪[K] 𝒪[F] F]
    [(IsDiscreteValuationRing.maximalIdeal 𝒪[F]).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).asIdeal]
    (eK : Multiplicative (ZMod n) ≃* Gal(U/K))
    (eF : Multiplicative (ZMod n) ≃* Gal(E/F))
    (hn : 1 < n)
    (NK : 𝒪[U]ˣ →* 𝒪[K]ˣ) (hNK : UnramifiedLocalData K U NK)
    (horderNormK : ∀ x : Uˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K U x)) =
        (n : ℤ) * localUnitOrder U (Additive.ofMul x))
    (NF : 𝒪[E]ˣ →* 𝒪[F]ˣ) (hNF : UnramifiedLocalData F E NF)
    (horderNormF : ∀ x : Eˣ,
      localUnitOrder F
          (Additive.ofMul (localNormUnits F E x)) =
        (n : ℤ) * localUnitOrder E (Additive.ofMul x))
    (a : Kˣ) :
    unramifiedInvariantEquiv F E eF hn NF hNF horderNormF
        (unramifiedCarryRelative F E eF
          (Units.map (algebraMap K F) a)) =
      (unramifiedInvariantEquiv K U eK hn NK hNK horderNormK
        (unramifiedCarryRelative K U eK a)) ^
        (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
          (IsLocalRing.maximalIdeal 𝒪[F]) := by
  apply unramified_invariant_carry K U F E
    eK eF hn NK hNK horderNormK NF hNF horderNormF
  exact algebra_ramification_idx K F a

/-- For a totally ramified extension, the ramification index is the full
field degree, so the transported carry invariant is raised to `[F : K]`.
This is the finite-invariant arithmetic required by formula (29) in the
totally ramified case. -/
theorem unramified_totally_ramified
    [Algebra 𝒪[K] 𝒪[F]] [Module.Finite 𝒪[K] 𝒪[F]]
    [Module.IsTorsionFree 𝒪[K] 𝒪[F]]
    [IsScalarTower 𝒪[K] K F] [IsScalarTower 𝒪[K] 𝒪[F] F]
    [(IsDiscreteValuationRing.maximalIdeal 𝒪[F]).asIdeal.LiesOver
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).asIdeal]
    (htotal : Towers.NumberTheory.Milne.TotallyRamified
      𝒪[K] 𝒪[F] (IsLocalRing.maximalIdeal 𝒪[K]))
    (eK : Multiplicative (ZMod n) ≃* Gal(U/K))
    (eF : Multiplicative (ZMod n) ≃* Gal(E/F))
    (hn : 1 < n)
    (NK : 𝒪[U]ˣ →* 𝒪[K]ˣ) (hNK : UnramifiedLocalData K U NK)
    (horderNormK : ∀ x : Uˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K U x)) =
        (n : ℤ) * localUnitOrder U (Additive.ofMul x))
    (NF : 𝒪[E]ˣ →* 𝒪[F]ˣ) (hNF : UnramifiedLocalData F E NF)
    (horderNormF : ∀ x : Eˣ,
      localUnitOrder F
          (Additive.ofMul (localNormUnits F E x)) =
        (n : ℤ) * localUnitOrder E (Additive.ofMul x))
    (a : Kˣ) :
    unramifiedInvariantEquiv F E eF hn NF hNF horderNormF
        (unramifiedCarryRelative F E eF
          (Units.map (algebraMap K F) a)) =
      (unramifiedInvariantEquiv K U eK hn NK hNK horderNormK
        (unramifiedCarryRelative K U eK a)) ^
        Module.finrank K F := by
  have hp0 : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field 𝒪[K]
  obtain ⟨P, hPprime, hPover, _hmap, hram, _hunique⟩ := htotal
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hPmax : P = IsLocalRing.maximalIdeal 𝒪[F] :=
    IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
  have hram' :
      (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
          (IsLocalRing.maximalIdeal 𝒪[F]) = Module.finrank 𝒪[K] 𝒪[F] := by
    simpa [hPmax] using hram
  have hfinrank : Module.finrank K F = Module.finrank 𝒪[K] 𝒪[F] :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing 𝒪[K] K 𝒪[F] F
  rw [hfinrank, ← hram']
  exact carry_ramification_idx
    K U F E eK eF hn NK hNK horderNormK NF hNF horderNormF a

end FiniteInvariant

end

end Towers.CField.LBrauer
