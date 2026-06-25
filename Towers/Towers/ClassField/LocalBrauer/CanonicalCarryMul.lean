import Towers.ClassField.CrossedProducts.SplitNonemptyHom
import Towers.ClassField.LocalBrauer.CanonicalCarryUnconditional
import Towers.ClassField.LocalBrauer.InvariantBaseChange
import Towers.ClassField.LocalBrauer.DivisionOrder

/-!
# Chapter IV, Section 4, Remark 4.4

The cohomological local invariant constructed in Proposition IV.4.3 is a
homomorphism.  At a finite unramified cyclic level of degree `n`, the `i`-th
power of Milne's carry crossed product has invariant `i / n` modulo integers,
and it is a division algebra when `i` is coprime to `n`.  Every local central
division algebra is the base field or one of these canonical carry crossed
products, with `n` equal to its degree and the exponent unique modulo `n`.
The splitting assertion in part (c) is reduced to the local-invariant
base-change formula cited there from Chapter III.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups CProduca

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- Remark IV.4.4(a): the local invariant respects the Brauer-group product. -/
theorem canonical_carry_invariant (x y : BrauerGroup K) :
    carryBrauerInvariant K (x * y) =
      carryBrauerInvariant K x *
        carryBrauerInvariant K y :=
  map_mul (carryBrauerInvariant K) x y

local instance canonicalCarryLocalBrauerInvariantMulDegreeNeZero (r : ℕ) :
    NeZero (invariantLevelDegree r) :=
  ⟨(invariant_level_pos r).ne'⟩

/-- The carry class at a canonical factorial level, regarded in the absolute
Brauer group. -/
noncomputable def canonicalCarryBrauer (r : ℕ) : BrauerGroup K :=
  ((FIData.carry K
      (factorialZMod K) r :
        brauerCofinalLevel K (unramifiedFactorialLevel K) r) :
    BrauerGroup K)

/-- The absolute local invariant of the `i`-th power of a canonical carry
class is `i / n`, where `n` is the degree of its unramified level. -/
theorem canonical_carry_coe
    (r i : ℕ) :
    (carryBrauerInvariant K
        ((canonicalCarryBrauer K r) ^ i)).toAdd =
      ((i : ℚ) / (invariantLevelDegree r : ℚ) : LocalInvariant) := by
  rw [map_pow, canonicalCarryBrauer,
    carry_brauer_invariant]
  change
    i • ((localDivTorsion (invariantLevelDegree r) :
      localInvariantTorsion (invariantLevelDegree r)) : LocalInvariant) = _
  rw [invariant_div_coe, ← AddCircle.coe_nsmul]
  congr 1
  ring

/-- A canonical carry class has order equal to the degree of its unramified
level; a coprime power remains a generator of the same order. -/
theorem order_carry_brauer
    (r i : ℕ) (hi : (invariantLevelDegree r).Coprime i) :
    orderOf ((canonicalCarryBrauer K r) ^ i) =
      invariantLevelDegree r := by
  let c := canonicalCarryBrauer K r
  let e := carryBrauerInvariant K
  have hcImage : (e c).toAdd =
      ((1 : ℚ) / (invariantLevelDegree r : ℚ) : LocalInvariant) := by
    simpa [c, e] using
      canonical_carry_coe K r 1
  have hgenerator : orderOf c = invariantLevelDegree r := by
    rw [← e.orderOf_eq c]
    change addOrderOf (e c).toAdd = invariantLevelDegree r
    rw [hcImage]
    simpa using AddCircle.addOrderOf_period_div
      (p := (1 : ℚ)) (invariant_level_pos r)
  have hi' : (orderOf c).Coprime i := by simpa [hgenerator] using hi
  change orderOf (c ^ i) = invariantLevelDegree r
  rw [hi'.orderOf_pow, hgenerator]

variable (L : Type u)
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra K L] [Module.Finite K L] [IsGalois K L]
  [Algebra 𝓀[K] 𝓀[L]]

variable {n : ℕ} [NeZero n]

/-- The finite invariant of the `i`-th power of the carry crossed product is
the `i`-th multiple of the generator `1 / n`. -/
theorem unramified_carry_pow
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1)
    (i : ℕ) :
    unramifiedInvariantEquiv K L eGal hn N hN horderNorm
        ((unramifiedCarryRelative K L eGal varpiK) ^ i) =
      (Multiplicative.ofAdd (localDivTorsion n)) ^ i := by
  rw [map_pow, unramified_equiv_carry
    K L eGal hn N hN horderNorm varpiK hvarpiK]

/-- Remark IV.4.4(b): in `ℚ/ℤ`, the invariant of `A(φ^i)` is `i / n`. -/
theorem invariant_carry_coe
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1)
    (i : ℕ) :
    ((unramifiedInvariantEquiv K L eGal hn N hN horderNorm
        ((unramifiedCarryRelative K L eGal varpiK) ^ i)).toAdd :
          LocalInvariant) =
      ((i : ℚ) / (n : ℚ) : LocalInvariant) := by
  rw [unramified_carry_pow
    K L eGal hn N hN horderNorm varpiK hvarpiK]
  change
    i • ((localDivTorsion n : localInvariantTorsion n) :
        LocalInvariant) = _
  rw [invariant_div_coe]
  rw [← AddCircle.coe_nsmul]
  congr 1
  ring

/-- If `i` is coprime to `n`, the `i`-th power of the carry crossed product
has order exactly `n` in the relative Brauer group.  This is the group-theoretic
content used in Remark IV.4.4(b) to identify the division representative. -/
theorem order_carry_relative
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1)
    (i : ℕ) (hi : n.Coprime i) :
    orderOf ((unramifiedCarryRelative K L eGal varpiK) ^ i) = n := by
  let e := unramifiedInvariantEquiv K L eGal hn N hN horderNorm
  let c := unramifiedCarryRelative K L eGal varpiK
  have hcImage : e c =
      Multiplicative.ofAdd (localDivTorsion n) :=
    unramified_equiv_carry
      K L eGal hn N hN horderNorm varpiK hvarpiK
  have hgenerator : orderOf c = n := by
    rw [← e.orderOf_eq c, hcImage]
    change addOrderOf (localDivTorsion n) = n
    rw [← (torsionZMod n).symm.addOrderOf_eq]
    simp [localDivTorsion, ZMod.addOrderOf_one]
  have hi' : (orderOf c).Coprime i := by simpa [hgenerator] using hi
  change orderOf (c ^ i) = n
  rw [hi'.orderOf_pow, hgenerator]

/-- Remark IV.4.4(b): when `i` is coprime to `n`, the crossed product
attached to the `i`-th power of the carry cocycle is a division algebra. -/
theorem carry_cocycle_domain
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1)
    (i : ℕ) (hi : n.Coprime i) :
    IsDomain
      (CProduc ((unramifiedCarryCocycle K L eGal varpiK) ^ i)) := by
  let c := unramifiedCarryCocycle K L eGal varpiK
  have hrelative :
      CProduc.relativeBrauerClass K L (c ^ i) =
        (unramifiedCarryRelative K L eGal varpiK) ^ i := by
    change
      (CProduc.hRelativeBrauer K L)
          (MHTwo.mk (c ^ i)) =
        ((CProduc.hRelativeBrauer K L)
          (MHTwo.mk c)) ^ i
    rw [← map_pow, MHTwo.mk_pow]
  have hrelativeOrder :
      orderOf (CProduc.relativeBrauerClass K L (c ^ i)) = n := by
    rw [hrelative]
    exact order_carry_relative
      K L eGal hn N hN horderNorm varpiK hvarpiK i hi
  have habsoluteOrder :
      orderOf (CProduc.brauerClass K L (c ^ i)) = n := by
    rw [show CProduc.brauerClass K L (c ^ i) =
        ((CProduc.relativeBrauerClass K L (c ^ i) :
          relativeBrauerGroup K L) : BrauerGroup K) by rfl,
      orderOf_submonoid]
    exact hrelativeOrder
  have hdegree : Module.finrank K L = n := by
    rw [← IsGalois.card_aut_eq_finrank]
    calc
      Nat.card Gal(L/K) = Nat.card (Multiplicative (ZMod n)) :=
        Nat.card_congr eGal.symm.toEquiv
      _ = n := by simp
  apply domain_sqrt_finrank K
  change orderOf (CProduc.brauerClass K L (c ^ i)) =
    Nat.sqrt (Module.finrank K (CProduc (c ^ i)))
  rw [habsoluteOrder, CProduc.finrank_over_base, hdegree]
  simp

/-- The same assertion packaged as the existence of the compatible division
ring structure on the crossed product. -/
theorem carry_cocycle_division
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1)
    (i : ℕ) (hi : n.Coprime i) :
    Nonempty
      (DivisionRing
        (CProduc ((unramifiedCarryCocycle K L eGal varpiK) ^ i))) := by
  letI : IsDomain
      (CProduc ((unramifiedCarryCocycle K L eGal varpiK) ^ i)) :=
    carry_cocycle_domain K L eGal hn N hN horderNorm
      varpiK hvarpiK i hi
  exact ⟨divisionRingOfFiniteDimensional K _⟩

/-- At a fixed canonical unramified level, carry crossed products are
isomorphic exactly when their exponents agree modulo the level degree. -/
theorem nonempty_carry_algebra
    (n : ℕ) [NeZero n] (hn : 1 < n) (i j : ℕ) :
    Nonempty
        (UnramifiedCarryAlgebra K n i ≃ₐ[K]
          UnramifiedCarryAlgebra K n j) ↔
      (i : ZMod n) = (j : ZMod n) := by
  rw [← carry_relative_brauer
    K n hn i j]
  constructor
  · rintro ⟨e⟩
    apply Subtype.ext
    change CProduc.brauerClass K (canonicalUnramifiedLevel K n)
        ((canonicalCarryCocycle K n) ^ i) =
      CProduc.brauerClass K (canonicalUnramifiedLevel K n)
        ((canonicalCarryCocycle K n) ^ j)
    apply (brauer_class K _ _).2
    exact brauer_equivalent_alg K _ _ e
  · intro hclass
    apply nonempty_equivalent_finrank K
      (UnramifiedCarryAlgebra K n i)
      (UnramifiedCarryAlgebra K n j)
    · apply (brauer_class K _ _).1
      exact congrArg Subtype.val hclass
    · rw [CProduc.finrank_over_base,
        CProduc.finrank_over_base]

/-- A central division algebra of degree one over `K` is `K` itself. -/
theorem nonempty_alg_sqrt
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (hdegree : Nat.sqrt (Module.finrank K D) = 1) :
    Nonempty (D ≃ₐ[K] K) := by
  have horder :
      orderOf (brauerClass K (centralDivisionCSA K D)) = 1 :=
    (brauer_division_finrank K D).trans hdegree
  have hclass : brauerClass K (centralDivisionCSA K D) = 1 :=
    orderOf_eq_one_iff.mp horder
  apply (division_brauer_equivalent K D K).1
  apply (brauer_class K _ _).1
  change brauerClass K (centralDivisionCSA K D) = 1
  exact hclass

/-- Remark IV.4.4(b): every nontrivial finite-dimensional central division
algebra over `K` is a canonical unramified carry crossed product.  The carry
exponent is coprime to the degree of the algebra. -/
theorem alg_carry_algebra
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (hn : 1 < Nat.sqrt (Module.finrank K D)) :
    let n := Nat.sqrt (Module.finrank K D)
    letI : NeZero n := ⟨(lt_trans Nat.zero_lt_one hn).ne'⟩
    ∃ i : ℕ, n.Coprime i ∧
        Nonempty
          (D ≃ₐ[K] UnramifiedCarryAlgebra K n i) := by
  dsimp only
  let n := Nat.sqrt (Module.finrank K D)
  have hnPos : 0 < n := lt_trans Nat.zero_lt_one hn
  letI : NeZero n := ⟨hnPos.ne'⟩
  let x := brauerClass K (centralDivisionCSA K D)
  have hperiod : orderOf x = n := by
    simpa [x, n] using
      brauer_division_finrank K D
  have hxpow : x ^ n = 1 := by
    rw [← hperiod]
    exact pow_orderOf_eq_one x
  have hxmem :
      x ∈ relativeBrauerGroup K (canonicalUnramifiedLevel K n) :=
    relative_brauer_level
      K n x hxpow
  let y : relativeBrauerGroup K (canonicalUnramifiedLevel K n) :=
    ⟨x, hxmem⟩
  have hyorder : orderOf y = n := by
    rw [← orderOf_submonoid y]
    exact hperiod
  obtain ⟨i, hi, hy⟩ :=
    coprime_carry_relative
      K n hn y hyorder
  have hclass :
      brauerClass K (centralDivisionCSA K D) =
        CProduc.brauerClass K (canonicalUnramifiedLevel K n)
          ((canonicalCarryCocycle K n) ^ i) := by
    change (y : BrauerGroup K) = _
    rw [hy, ← canonical_unramified_carry]
    rfl
  obtain ⟨d, hd⟩ := finrank_simple_square K D
  have hDdim : Module.finrank K D = n ^ 2 := by
    rw [hd]
    simp [n, hd]
  have hCarryDim :
      Module.finrank K (UnramifiedCarryAlgebra K n i) = n ^ 2 := by
    change Module.finrank K
      (CProduc ((canonicalCarryCocycle K n) ^ i)) = n ^ 2
    rw [CProduc.finrank_over_base,
      unramified_level_finrank K n]
  have hBrauer : IsBrauerEquivalent
      (centralDivisionCSA K D)
      (centralSimpleCSA K (UnramifiedCarryAlgebra K n i)) := by
    apply (brauer_class K _ _).1
    exact hclass
  refine ⟨i, hi, ?_⟩
  exact nonempty_equivalent_finrank
    K D (UnramifiedCarryAlgebra K n i) hBrauer
      (hDdim.trans hCarryDim.symm)

/-- Remark IV.4.4(b), exhaustive form: a finite-dimensional central division
algebra is either the base field (degree one), or a coprime power of the carry
crossed product for the canonical unramified extension of its degree. -/
theorem division_or_carry
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D] :
    let n := Nat.sqrt (Module.finrank K D)
    Nonempty (D ≃ₐ[K] K) ∨
      ∃ hn : 1 < n,
        letI : NeZero n := ⟨(lt_trans Nat.zero_lt_one hn).ne'⟩
        ∃ i : ℕ, n.Coprime i ∧
          Nonempty (D ≃ₐ[K] UnramifiedCarryAlgebra K n i) := by
  dsimp only
  let n := Nat.sqrt (Module.finrank K D)
  let x := brauerClass K (centralDivisionCSA K D)
  have hperiod : orderOf x = n := by
    simpa [x, n] using
      brauer_division_finrank K D
  have hnPos : 0 < n := by
    rw [← hperiod]
    exact (brauer_group_torsion K x).orderOf_pos
  by_cases hnOne : n = 1
  · exact Or.inl
      (nonempty_alg_sqrt K D
        (by simpa [n] using hnOne))
  · have hn : 1 < n :=
      (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨hnPos.ne', hnOne⟩
    refine Or.inr ⟨hn, ?_⟩
    simpa [n] using
      alg_carry_algebra K D (by simpa [n] using hn)

omit [IsGalois K L] [Algebra 𝓀[K] 𝓀[L]] [Module.Finite K L] in
/-- Remark IV.4.4(c), reduced to the cited base-change formula from Chapter
III: if scalar extension multiplies the local invariant by `[L : K]`, then
every extension whose degree equals the degree of `D` splits `D`. -/
theorem split_brauer_change
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (hdegree : Module.finrank K L = Nat.sqrt (Module.finrank K D))
    (hbaseChange :
      carryBrauerInvariant L
          (brauerBaseChange K L
            (brauerClass K (centralDivisionCSA K D))) =
        (carryBrauerInvariant K
          (brauerClass K (centralDivisionCSA K D))) ^
            Module.finrank K L) :
    ISBy K L D := by
  let x := brauerClass K (centralDivisionCSA K D)
  have hperiod : orderOf x = Nat.sqrt (Module.finrank K D) := by
    simpa [x] using
      brauer_division_finrank K D
  have hinvariantPow :
      (carryBrauerInvariant K x) ^ Module.finrank K L = 1 := by
    rw [hdegree, ← hperiod, ← map_pow, pow_orderOf_eq_one, map_one]
  have hbaseOne :
      carryBrauerInvariant L (brauerBaseChange K L x) = 1 := by
    rw [hbaseChange, hinvariantPow]
  have hclassOne : brauerBaseChange K L x = 1 := by
    apply (carryBrauerInvariant L).injective
    simpa using hbaseOne
  have hxmem : x ∈ relativeBrauerGroup K L :=
    (relative_brauer_group K L x).2 hclassOne
  exact (brauer_relative_split
    K L (centralDivisionCSA K D)).1 hxmem

omit [IsGalois K L] [Algebra 𝓀[K] 𝓀[L]] [Module.Finite K L] in
/-- Remark IV.4.4(c), using the packaged local-invariant base-change
formula. -/
theorem split_change_formula
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (hdegree : Module.finrank K L = Nat.sqrt (Module.finrank K D))
    (hbaseChange : BCForm K L) :
    ISBy K L D :=
  split_brauer_change K L D hdegree
    (hbaseChange (brauerClass K (centralDivisionCSA K D)))

/-- Remark IV.4.4(c) for an abstract finite extension with its canonical
spectral local-field structure, reduced only to formula (29) of Chapter III.
No Galois hypothesis is required. -/
theorem split_spectral_formula
    (F : Type u) [Field F] [Algebra K F] [FiniteDimensional K F]
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (hdegree : Module.finrank K F = Nat.sqrt (Module.finrank K D))
    (hbaseChange : SpectralChangeFormula K F) :
    ISBy K F D := by
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  letI : NontriviallyNormedField F :=
    FLExt.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  letI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := FLExt.valuativeRel K F
  letI : Valuation.Compatible (NormedField.valuation (K := F)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := F))
  letI : IsNonarchimedeanLocalField F :=
    FLExt.nonarchimedeanLocalField K F
  exact split_change_formula K F D hdegree hbaseChange

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The final algebraic step in Remark IV.4.4(c): if the field generated by
one root of an irreducible polynomial splits a division algebra of the
matching degree, then that polynomial already has a root in the division
algebra. -/
theorem division_adjoin_split
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (f : Polynomial K) [hf : Fact (Irreducible f)]
    (hD : Module.finrank K D = f.natDegree ^ 2)
    (hsplit : ISBy K (AdjoinRoot f) D) :
    ∃ x : D, Polynomial.eval₂ (algebraMap K D) x f = 0 := by
  letI : Module.Finite K (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hf.out.ne_zero).finite
  have hL : Module.finrank K (AdjoinRoot f) = f.natDegree :=
    (AdjoinRoot.powerBasis hf.out.ne_zero).finrank
  obtain ⟨i⟩ :=
    (split_nonempty_alg K (AdjoinRoot f) D f.natDegree hD hL).1
      hsplit
  refine ⟨i (AdjoinRoot.root f), ?_⟩
  have hcomp : i.toRingHom.comp (AdjoinRoot.of f) = algebraMap K D := by
    ext a
    exact i.commutes a
  rw [← hcomp]
  calc
    Polynomial.eval₂ (i.toRingHom.comp (AdjoinRoot.of f))
        (i (AdjoinRoot.root f)) f =
      i (Polynomial.eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) f) :=
        (Polynomial.hom_eval₂ f (AdjoinRoot.of f) i.toRingHom
          (AdjoinRoot.root f)).symm
    _ = 0 := by rw [AdjoinRoot.eval₂_root, map_zero]

/-- Remark IV.4.4(c), polynomial form, reduced only to the spectral
local-invariant base-change formula for the adjoining-root extension. -/
theorem division_spectral_formula
    (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [Module.Finite K D]
    (f : Polynomial K) [hf : Fact (Irreducible f)]
    (hD : Module.finrank K D = f.natDegree ^ 2)
    (hbaseChange :
      letI : Module.Finite K (AdjoinRoot f) :=
        (AdjoinRoot.powerBasis hf.out.ne_zero).finite
      SpectralChangeFormula K (AdjoinRoot f)) :
    ∃ x : D, Polynomial.eval₂ (algebraMap K D) x f = 0 := by
  letI : Module.Finite K (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hf.out.ne_zero).finite
  have hL : Module.finrank K (AdjoinRoot f) = f.natDegree :=
    (AdjoinRoot.powerBasis hf.out.ne_zero).finrank
  have hsqrt : Nat.sqrt (Module.finrank K D) = f.natDegree := by
    rw [hD]
    simp
  have hsplit : ISBy K (AdjoinRoot f) D :=
    split_spectral_formula
      K (AdjoinRoot f) D (hL.trans hsqrt.symm) hbaseChange
  exact division_adjoin_split
    K D f hD hsplit

end

end Towers.CField.LBrauer
