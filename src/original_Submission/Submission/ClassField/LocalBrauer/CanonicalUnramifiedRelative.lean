import Submission.ClassField.LocalBrauer.CanonicalCarryUnconditional
import Submission.ClassField.LocalBrauer.CanonicalUnramifiedData
import Submission.ClassField.CrossedProducts.IsMulCoboundary

/-!
# Relative Brauer groups at arbitrary canonical unramified levels

The arithmetic data used for the factorial tower is available at every
positive canonical unramified level.  This file packages the resulting
equivalence of its relative Brauer group with `ZMod n`.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups CProduca

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev canonicalField (n : ℕ) := canonicalUnramifiedLevel K n

local instance canonicalFieldAlgebraic (n : ℕ) :
    Algebra.IsAlgebraic K (canonicalField K n) :=
  Algebra.IsAlgebraic.of_finite K (canonicalField K n)

local instance canonicalFieldNontriviallyNormedField (n : ℕ) :
    NontriviallyNormedField (canonicalField K n) :=
  FLExt.nontriviallyNormedField K (canonicalField K n)

local instance canonicalFieldNormedAlgebra (n : ℕ) :
    NormedAlgebra K (canonicalField K n) :=
  spectralNorm.normedAlgebra K (canonicalField K n)

local instance canonicalFieldIsUltrametricDist (n : ℕ) :
    IsUltrametricDist (canonicalField K n) :=
  IsUltrametricDist.of_normedAlgebra K

local instance canonicalFieldValuativeRel (n : ℕ) :
    ValuativeRel (canonicalField K n) :=
  FLExt.valuativeRel K (canonicalField K n)

local instance canonicalFieldValuationCompatible (n : ℕ) :
    Valuation.Compatible
      (NormedField.valuation (K := canonicalField K n)) :=
  Valuation.Compatible.ofValuation
    (NormedField.valuation (K := canonicalField K n))

local instance canonicalFieldIsLocalField (n : ℕ) :
    IsNonarchimedeanLocalField (canonicalField K n) :=
  FLExt.nonarchimedeanLocalField K (canonicalField K n)

private theorem canonical_invariant_data (n : ℕ) [NeZero n] :
    ∃ hResidueAlgebra : Algebra 𝓀[K] 𝓀[canonicalField K n],
      letI : Algebra 𝓀[K] 𝓀[canonicalField K n] := hResidueAlgebra
      UnramifiedUnitData K (canonicalField K n)
          (FLExt.integerUnitNorm K (canonicalField K n)) ∧
        ∀ x : Kˣ,
          localUnitOrder (canonicalField K n)
              (Additive.ofMul
                (Units.map (algebraMap K (canonicalField K n)) x)) =
            localUnitOrder K (Additive.ofMul x) := by
  obtain ⟨hResidueAlgebra, hUnit, horder, _⟩ :=
    unramified_level_data K n
  exact ⟨hResidueAlgebra, hUnit, horder⟩

@[implicit_reducible]
private noncomputable def canonicalResidueAlgebra
    (n : ℕ) [NeZero n] :
    Algebra 𝓀[K] 𝓀[canonicalField K n] :=
  Classical.choose (canonical_invariant_data K n)

private theorem canonicalUnitData (n : ℕ) [NeZero n] :
    letI : Algebra 𝓀[K] 𝓀[canonicalField K n] :=
      canonicalResidueAlgebra K n
    UnramifiedUnitData K (canonicalField K n)
      (FLExt.integerUnitNorm K (canonicalField K n)) :=
  (Classical.choose_spec (canonical_invariant_data K n)).1

private theorem canonical_order_algebra
    (n : ℕ) [NeZero n] (x : Kˣ) :
    localUnitOrder (canonicalField K n)
        (Additive.ofMul
          (Units.map (algebraMap K (canonicalField K n)) x)) =
      localUnitOrder K (Additive.ofMul x) :=
  (Classical.choose_spec (canonical_invariant_data K n)).2 x

private theorem canonicalNormData (n : ℕ) [NeZero n] :
    letI : Algebra 𝓀[K] 𝓀[canonicalField K n] :=
      canonicalResidueAlgebra K n
    UnramifiedLocalData K (canonicalField K n)
      (FLExt.integerUnitNorm K (canonicalField K n)) := by
  letI : Algebra 𝓀[K] 𝓀[canonicalField K n] :=
    canonicalResidueAlgebra K n
  exact FLExt.unramified_data_unit K
    (canonicalField K n) (canonicalResidueAlgebra K n)
    (canonicalUnitData K n)

private theorem canonical_order_norm (n : ℕ) [NeZero n]
    (x : (canonicalField K n)ˣ) :
    localUnitOrder K
        (Additive.ofMul (localNormUnits K (canonicalField K n) x)) =
      (n : ℤ) *
        localUnitOrder (canonicalField K n) (Additive.ofMul x) := by
  rw [show localNormUnits K (canonicalField K n) x =
      Units.map (Algebra.norm K) x by rfl]
  apply UOExt.order_norm_finrankeq K
    (canonicalField K n)
  · exact
      { order_algebraMap := canonical_order_algebra K n
        order_aut := FLExt.unit_order_aut K
          (canonicalField K n) }
  · exact unramified_level_finrank K n

/-- The relative Brauer group of the canonical unramified degree-`n` level
is cyclic of order `n`. -/
noncomputable def brauerZMod
    (n : ℕ) [NeZero n] (hn : 1 < n) :
    relativeBrauerGroup K (canonicalUnramifiedLevel K n) ≃*
      Multiplicative (ZMod n) := by
  letI : Algebra 𝓀[K] 𝓀[canonicalField K n] :=
    canonicalResidueAlgebra K n
  exact unramifiedZMod K (canonicalField K n)
    (galZMod K n) hn
    (FLExt.integerUnitNorm K (canonicalField K n))
    (canonicalNormData K n)
    (canonical_order_norm K n)

/-- The carry cocycle on the canonical unramified extension of degree `n`.
This wrapper fixes the canonical spectral norm used on that extension. -/
noncomputable def canonicalCarryCocycle
    (n : ℕ) [NeZero n] :
    NMCocycl₂
      (G := Gal((canonicalUnramifiedLevel K n)/K))
      (M := (canonicalUnramifiedLevel K n)ˣ) :=
  unramifiedCarryCocycle K (canonicalUnramifiedLevel K n)
    (galZMod K n)
    (canonicalLocalUniformizer K)

/-- The canonical carry crossed product with exponent `i`. -/
abbrev UnramifiedCarryAlgebra (n i : ℕ) [NeZero n] :=
  CProduc ((canonicalCarryCocycle K n) ^ i)

/-- The relative Brauer class of the canonical carry algebra is the
corresponding power of the carry generator. -/
theorem canonical_unramified_carry
    (n i : ℕ) [NeZero n] :
    CProduc.relativeBrauerClass K (canonicalUnramifiedLevel K n)
        ((canonicalCarryCocycle K n) ^ i) =
      (unramifiedCarryRelative K
        (canonicalUnramifiedLevel K n)
        (galZMod K n)
        (canonicalLocalUniformizer K)) ^ i := by
  change
    (CProduc.hRelativeBrauer K
      (canonicalUnramifiedLevel K n))
        (MHTwo.mk
          ((canonicalCarryCocycle K n) ^ i)) =
      ((CProduc.hRelativeBrauer K
        (canonicalUnramifiedLevel K n))
          (MHTwo.mk
            (canonicalCarryCocycle K n))) ^ i
  rw [← map_pow, MHTwo.mk_pow]

/-- The canonical relative invariant sends the carry generator to `1`. -/
theorem brauer_z_carry
    (n : ℕ) [NeZero n] (hn : 1 < n) :
    brauerZMod K n hn
        (unramifiedCarryRelative K
          (canonicalUnramifiedLevel K n)
          (galZMod K n)
          (canonicalLocalUniformizer K)) =
      Multiplicative.ofAdd (1 : ZMod n) := by
  letI : Algebra 𝓀[K] 𝓀[canonicalField K n] :=
    canonicalResidueAlgebra K n
  exact relative_z_carry K
    (canonicalField K n)
    (galZMod K n) hn
    (FLExt.integerUnitNorm K (canonicalField K n))
    (canonicalNormData K n)
    (canonical_order_norm K n)
    (canonicalLocalUniformizer K)
    (canonical_uniformizer_order K)

/-- Canonical carry powers have the same relative Brauer class exactly when
their exponents agree modulo the extension degree. -/
theorem carry_relative_brauer
    (n : ℕ) [NeZero n] (hn : 1 < n) (i j : ℕ) :
    CProduc.relativeBrauerClass K (canonicalUnramifiedLevel K n)
        ((canonicalCarryCocycle K n) ^ i) =
      CProduc.relativeBrauerClass K (canonicalUnramifiedLevel K n)
        ((canonicalCarryCocycle K n) ^ j) ↔
      (i : ZMod n) = (j : ZMod n) := by
  rw [canonical_unramified_carry,
    canonical_unramified_carry]
  let e := brauerZMod K n hn
  have hcarry : e (unramifiedCarryRelative K
      (canonicalUnramifiedLevel K n)
      (galZMod K n)
      (canonicalLocalUniformizer K)) =
      Multiplicative.ofAdd (1 : ZMod n) :=
    brauer_z_carry K n hn
  constructor
  · intro h
    have h' :
        (e (unramifiedCarryRelative K
          (canonicalUnramifiedLevel K n)
          (galZMod K n)
          (canonicalLocalUniformizer K))) ^ i =
        (e (unramifiedCarryRelative K
          (canonicalUnramifiedLevel K n)
          (galZMod K n)
          (canonicalLocalUniformizer K))) ^ j := by
      simpa only [map_pow] using congrArg e h
    rw [hcarry] at h'
    have h'' := congrArg Multiplicative.toAdd h'
    simpa using h''
  · intro h
    apply e.injective
    simp only [map_pow, hcarry]
    rw [← ofAdd_nsmul, ← ofAdd_nsmul]
    simpa using congrArg Multiplicative.ofAdd h

/-- Every class at the canonical unramified degree-`n` level is a power of
its carry crossed product. -/
theorem unramified_carry_relative
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (x : relativeBrauerGroup K (canonicalUnramifiedLevel K n)) :
    ∃ i : ℕ,
      x = (unramifiedCarryRelative K
        (canonicalUnramifiedLevel K n)
        (galZMod K n)
        (canonicalLocalUniformizer K)) ^ i := by
  letI : Algebra 𝓀[K] 𝓀[canonicalField K n] :=
    canonicalResidueAlgebra K n
  obtain ⟨i, hi⟩ := unramified_carry_brauer K
    (canonicalField K n)
    (galZMod K n) hn
    (FLExt.integerUnitNorm K (canonicalField K n))
    (canonicalNormData K n)
    (canonical_order_norm K n)
    (canonicalLocalUniformizer K)
    (canonical_uniformizer_order K) x
  exact ⟨i.val, hi⟩

/-- If a class at the degree-`n` canonical level has order `n`, its carry
exponent can be chosen coprime to `n`. -/
theorem coprime_carry_relative
    (n : ℕ) [NeZero n] (hn : 1 < n)
    (x : relativeBrauerGroup K (canonicalUnramifiedLevel K n))
    (horder : orderOf x = n) :
    ∃ i : ℕ, n.Coprime i ∧
      x = (unramifiedCarryRelative K
        (canonicalUnramifiedLevel K n)
        (galZMod K n)
        (canonicalLocalUniformizer K)) ^ i := by
  obtain ⟨i, hi⟩ :=
    unramified_carry_relative K n hn x
  letI : Algebra 𝓀[K] 𝓀[canonicalField K n] :=
    canonicalResidueAlgebra K n
  let e := brauerZMod K n hn
  have hcarry : e (unramifiedCarryRelative K
      (canonicalField K n)
      (galZMod K n)
      (canonicalLocalUniformizer K)) =
      Multiplicative.ofAdd (1 : ZMod n) := by
    exact relative_z_carry K
      (canonicalField K n)
      (galZMod K n) hn
      (FLExt.integerUnitNorm K (canonicalField K n))
      (canonicalNormData K n)
      (canonical_order_norm K n)
      (canonicalLocalUniformizer K)
      (canonical_uniformizer_order K)
  have heOrder : orderOf (e x) = n := by
    rw [e.orderOf_eq, horder]
  rw [hi, map_pow, hcarry] at heOrder
  have hiOrder : addOrderOf (i : ZMod n) = n := by
    rw [← ofAdd_nsmul] at heOrder
    simpa using heOrder
  have hdiv : n / n.gcd i = n := by
    simpa [ZMod.addOrderOf_coe i (NeZero.ne n)] using hiOrder
  have hgcdPos : 0 < n.gcd i := Nat.gcd_pos_of_pos_left i (NeZero.pos n)
  have hnMul : n = n * n.gcd i :=
    (Nat.div_eq_iff_eq_mul_left hgcdPos (Nat.gcd_dvd_left n i)).1 hdiv
  have hgcd : n.gcd i = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
    simpa using hnMul.symm
  exact ⟨i, hgcd, hi⟩

/-- The subgroup of the multiplicative local invariant group killed by
`n`. -/
def localPowTorsion (n : ℕ) :
    Subgroup (Multiplicative LocalInvariant) where
  carrier := {x | x ^ n = 1}
  one_mem' := one_pow n
  mul_mem' := by
    intro x y hx hy
    change x ^ n = 1 at hx
    change y ^ n = 1 at hy
    change (x * y) ^ n = 1
    rw [mul_pow, hx, hy, one_mul]
  inv_mem' := by
    intro x hx
    change x ^ n = 1 at hx
    change x⁻¹ ^ n = 1
    rw [inv_pow, hx, inv_one]

/-- The additive and multiplicative descriptions of the `n`-torsion in
`ℚ/ℤ` agree. -/
noncomputable def localTorsionPow (n : ℕ) :
    Multiplicative (localInvariantTorsion n) ≃*
      localPowTorsion n where
  toFun x := ⟨Multiplicative.ofAdd (x.toAdd : LocalInvariant), by
    change n • ((x.toAdd : localInvariantTorsion n) : LocalInvariant) = 0
    exact x.toAdd.property⟩
  invFun x := Multiplicative.ofAdd ⟨x.1.toAdd, by
    change x.1 ^ n = 1
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Every Brauer class killed by `n` is split by the canonical unramified
extension of degree `n`.  This follows from the uniqueness of the order-`n`
subgroup of `ℚ/ℤ`: the canonical relative Brauer group has `n` elements and
all of them are killed by `n`. -/
theorem relative_brauer_level
    (n : ℕ) [NeZero n] (x : BrauerGroup K) (hx : x ^ n = 1) :
    x ∈ relativeBrauerGroup K (canonicalUnramifiedLevel K n) := by
  by_cases hnOne : n = 1
  · subst n
    rw [pow_one] at hx
    rw [hx]
    exact Subgroup.one_mem _
  have hn : 1 < n :=
    (Nat.one_lt_iff_ne_zero_and_ne_one).2 ⟨NeZero.ne n, hnOne⟩
  let H := relativeBrauerGroup K (canonicalUnramifiedLevel K n)
  let T := localPowTorsion n
  let eH : H ≃* Multiplicative (ZMod n) :=
    brauerZMod K n hn
  let eT : Multiplicative (ZMod n) ≃* T :=
    (torsionZMod n).toMultiplicative.trans
      (localTorsionPow n)
  let eInv := carryBrauerInvariant K
  let f : H → T := fun y ↦ ⟨eInv (y : BrauerGroup K), by
    have hy := relative_brauer_one K
      (canonicalUnramifiedLevel K n) y
    rw [unramified_level_finrank K n] at hy
    have hyAbs : ((y : BrauerGroup K) ^ n) = 1 :=
      congrArg Subtype.val hy
    change (eInv (y : BrauerGroup K)) ^ n = 1
    rw [← map_pow, hyAbs, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply eInv.injective
    exact congrArg Subtype.val hab
  letI : Finite H := Finite.of_injective eH eH.injective
  letI : Finite T := Finite.of_injective eT.symm eT.symm.injective
  have hcard : Nat.card H = Nat.card T := by
    calc
      Nat.card H = Nat.card (Multiplicative (ZMod n)) :=
        Nat.card_congr eH.toEquiv
      _ = Nat.card T := Nat.card_congr eT.toEquiv
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).2 ⟨hf, hcard⟩).2
  let q : T := ⟨eInv x, by
    change (eInv x) ^ n = 1
    rw [← map_pow, hx, map_one]⟩
  obtain ⟨y, hy⟩ := hsurj q
  have hyVal : (y : BrauerGroup K) = x := by
    apply eInv.injective
    exact congrArg Subtype.val hy
  rw [← hyVal]
  exact y.property

/-- A class is split by the canonical unramified extension whose degree is
the order of the class. -/
theorem relative_level_order
    (x : BrauerGroup K) (hx : 0 < orderOf x) :
    x ∈ relativeBrauerGroup K
      (canonicalUnramifiedLevel K (orderOf x)) := by
  letI : NeZero (orderOf x) := ⟨hx.ne'⟩
  exact relative_brauer_level
    K (orderOf x) x (pow_orderOf_eq_one x)

end

end Submission.CField.LBrauer
