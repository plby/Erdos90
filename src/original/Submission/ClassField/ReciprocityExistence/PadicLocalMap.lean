import Submission.ClassField.LubinTate.CyclotomicResidueDegree
import Submission.ClassField.LubinTate.LocalArtinMap
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-!
# The conductor-prime local map in Example VII.8.2

This file upgrades the coordinate description of the ramified factor from
`Z_p^x x Z` to a homomorphism on the actual group `Q_p^x`, using the
unit--uniformizer decomposition from Chapter I.
-/

namespace Submission.CField.RExist

open Polynomial
open Submission.CField.LTate

noncomputable section

private instance padicValuationDiscrete
    (p : ℕ) [Fact p.Prime] :
    (Padic.mulValuation (p := p)).IsRankOneDiscrete := by
  infer_instance

/-- The valuation ring for the standard multiplicative valuation on `Q_p`
maps identically to the usual ring `Z_p`. -/
private noncomputable def padicSubringInt
    (p : ℕ) [Fact p.Prime] :
    (Padic.mulValuation (p := p)).valuationSubring →+* ℤ_[p] where
  toFun x := ⟨x, by
    classical
    rw [Padic.norm_le_one_iff_val_nonneg]
    by_cases hx : (x : ℚ_[p]) = 0
    · simp [hx]
    · have hxval : Padic.mulValuation (x : ℚ_[p]) ≤ 1 := x.property
      change (if (x : ℚ_[p]) = 0 then 0 else
        WithZero.exp (-(x : ℚ_[p]).valuation)) ≤ 1 at hxval
      simp only [hx, if_false, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at hxval
      omega⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Conversely, a `p`-adic integer belongs to the valuation ring of the
standard multiplicative valuation. -/
private noncomputable def padicValuationSubring
    (p : ℕ) [Fact p.Prime] :
    ℤ_[p] →+* (Padic.mulValuation (p := p)).valuationSubring where
  toFun x := ⟨x, by
    classical
    have hxnorm : ‖(x : ℚ_[p])‖ ≤ 1 := x.property
    rw [Padic.norm_le_one_iff_val_nonneg] at hxnorm
    by_cases hx : (x : ℚ_[p]) = 0
    · simp [hx]
    · change (if (x : ℚ_[p]) = 0 then 0 else
        WithZero.exp (-(x : ℚ_[p]).valuation)) ≤ 1
      simp only [hx, if_false, ← WithZero.exp_zero,
        WithZero.exp_le_exp]
      omega⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The valuation ring of the standard valuation on `Q_p` is canonically
the usual ring `Z_p`; both maps are the identity on underlying elements. -/
private noncomputable def valuationSubringInt
    (p : ℕ) [Fact p.Prime] :
    (Padic.mulValuation (p := p)).valuationSubring ≃+* ℤ_[p] where
  toFun := padicSubringInt p
  invFun := padicValuationSubring p
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The standard multiplicative valuation on `Q_p` is onto `Z^m_0`. -/
theorem padic_valuation_surjective
    (p : ℕ) [Fact p.Prime] :
    Function.Surjective (Padic.mulValuation (p := p)) := by
  intro z
  obtain ⟨q, hq⟩ := Rat.surjective_padicValuation p z
  refine ⟨(q : ℚ_[p]), ?_⟩
  have h := DFunLike.congr_fun
    (Padic.comap_mulValuation_eq_padicValuation (p := p)) q
  exact h.trans hq

/-- The rational prime `p` is a uniformizer of `Q_p`. -/
theorem padic_prime_uniformizer
    (p : ℕ) [Fact p.Prime] :
    (Padic.mulValuation (p := p)).IsUniformizer (p : ℚ_[p]) := by
  rw [Valuation.IsUniformizer.iff]
  rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
    (padic_valuation_surjective p)]
  have h := DFunLike.congr_fun
    (Padic.comap_mulValuation_eq_padicValuation (p := p)) (p : ℚ)
  exact h.trans (Rat.padicValuation_self p)

/-- Reduction from `Z_p` to `Z/p^r Z` is onto. -/
theorem int_z_surjective
    (p r : ℕ) [Fact p.Prime] :
    Function.Surjective (PadicInt.toZModPow (p := p) r) := by
  intro x
  refine ⟨((x.val : ℕ) : ℤ_[p]), ?_⟩
  calc
    PadicInt.toZModPow r ((x.val : ℕ) : ℤ_[p]) =
        ((x.val : ℕ) : ZMod (p ^ r)) := map_natCast _ _
    _ = x := by simp

/-- For a positive level, every invertible residue class modulo `p^r`
lifts to a `p`-adic unit. -/
theorem padic_reduction_surjective
    (p r : ℕ) [Fact p.Prime] (hr : 0 < r) :
    Function.Surjective (padicUnitReduction p r) := by
  letI : Fact (1 < p ^ r) :=
    ⟨Nat.one_lt_pow (Nat.ne_of_gt hr) (Fact.out : p.Prime).one_lt⟩
  apply IsLocalRing.surjective_units_map_of_local_ringHom
      (PadicInt.toZModPow (p := p) r)
      (int_z_surjective p r)
  exact Function.Surjective.isLocalHom _
    (int_z_surjective p r)

/-- Units in the valuation ring of `Q_p`, identified with the conventional
unit group `Z_p^x`. -/
noncomputable def padicValuationInt
    (p : ℕ) [Fact p.Prime] :
    (Padic.mulValuation (p := p)).valuationSubring.unitGroup ≃* ℤ_[p]ˣ :=
  (Padic.mulValuation (p := p)).valuationSubring.unitGroupMulEquiv |>.trans
    (Units.mapEquiv (valuationSubringInt p).toMulEquiv)

/-- The inverse-unit cyclotomic action, transported to the unit group of the
valuation ring used by the local multiplicative decomposition. -/
noncomputable def padicValuationAction
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    (Padic.mulValuation (p := p)).valuationSubring.unitGroup →* Gal(L/ℚ) :=
  (padicCyclotomicAction p r
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
    (L := L)).comp (padicValuationInt p).toMonoidHom

private theorem valuation_action_commute
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (u : (Padic.mulValuation (p := p)).valuationSubring.unitGroup) :
    Commute (padicValuationAction p r L u) 1 :=
  Commute.one_right _

/-- **Example I.3.13(b), on its actual local domain.**  For the totally
ramified `p^r`-cyclotomic extension, the explicit local map on `Q_p^x` is
the inverse-unit action and is trivial on the uniformizer `p`. -/
noncomputable def padicCyclotomicArtin
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    ℚ_[p]ˣ →* Gal(L/ℚ) :=
  artinCommutingActions
    (Padic.mulValuation (p := p)) (p : ℚ_[p])
    (padic_prime_uniformizer p)
    (padicValuationAction p r L) 1
    (valuation_action_commute p r L)

/-- On the unique decomposition `a = u * p^m`, the explicit local map is
exactly the inverse residue-class action of `u`; the exponent `m` has no
effect. -/
theorem padic_artin_decomposition
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (u : (Padic.mulValuation (p := p)).valuationSubring.unitGroup)
    (m : ℤ) :
    padicCyclotomicArtin p r L
        ((u : ℚ_[p]ˣ) *
          (Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero) ^ m) =
      padicValuationAction p r L u := by
  simpa [padicCyclotomicArtin] using
    commuting_actions_decomposition
      (Padic.mulValuation (p := p)) (p : ℚ_[p])
      (padic_prime_uniformizer p)
      (padicValuationAction p r L) 1
      (valuation_action_commute p r L) u m

@[simp]
theorem padic_valuation_coe
    (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    ((((padicValuationInt p).symm u :
        (Padic.mulValuation (p := p)).valuationSubring.unitGroup) :
        ℚ_[p]ˣ) : ℚ_[p]) = (u : ℤ_[p]) :=
  rfl

/-- The source's displayed formula: if `a = u p^m` with
`u ∈ Z_p^x`, then `a` acts on the `p^r`-th roots of unity through the
inverse residue class of `u`. -/
theorem padic_artin_zpow
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (u : ℤ_[p]ˣ) (m : ℤ) :
    padicCyclotomicArtin p r L
        ((((padicValuationInt p).symm u :
            (Padic.mulValuation (p := p)).valuationSubring.unitGroup) :
            ℚ_[p]ˣ) *
          (Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero) ^ m) =
      padicCyclotomicAction p r
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        (L := L) u := by
  rw [padic_artin_decomposition]
  simp [padicValuationAction]

/-- At a positive prime-power level, the inverse-unit action realizes every
cyclotomic automorphism. -/
theorem padic_action_surjective
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)] (hr : 0 < r)
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    Function.Surjective
      (padicCyclotomicAction p r
        (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
        (L := L)) := by
  intro σ
  let e := IsCyclotomicExtension.autEquivPow L
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r)))
  obtain ⟨u, hu⟩ := padic_reduction_surjective p r hr (e σ)
  refine ⟨u⁻¹, ?_⟩
  change e.symm (padicUnitReduction p r (u⁻¹)⁻¹) = σ
  rw [inv_inv, hu, e.symm_apply_apply]

/-- Hence the explicit local map on `Q_p^x` is surjective, as local
reciprocity predicts. -/
theorem padic_artin_surjective
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)] (hr : 0 < r)
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    Function.Surjective (padicCyclotomicArtin p r L) := by
  intro σ
  obtain ⟨u, hu⟩ := padic_action_surjective p r hr L σ
  refine ⟨((padicValuationInt p).symm u : ℚ_[p]ˣ), ?_⟩
  have h := padic_artin_zpow
    p r L u 0
  simpa using h.trans hu

/-- Equivalently, `u p^m` sends the chosen primitive root to the power
indexed by `u₀⁻¹`, exactly as displayed in Example I.3.13(b). -/
theorem padic_artin_zeta
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (u : ℤ_[p]ˣ) (m : ℤ) :
    padicCyclotomicArtin p r L
        ((((padicValuationInt p).symm u :
            (Padic.mulValuation (p := p)).valuationSubring.unitGroup) :
            ℚ_[p]ˣ) *
          (Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero) ^ m)
        (IsCyclotomicExtension.zeta (p ^ r) ℚ L) =
      IsCyclotomicExtension.zeta (p ^ r) ℚ L ^
        ((padicUnitReduction p r u⁻¹ : ZMod (p ^ r)).val) := by
  rw [padic_artin_zpow]
  exact padic_action_zeta p r
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r))) u

/-- In particular the uniformizer has trivial image, as the extension is
totally ramified. -/
theorem padic_artin_uniformizer
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L] :
    padicCyclotomicArtin p r L
        (Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero) = 1 := by
  simpa using padic_artin_zpow
    p r L (1 : ℤ_[p]ˣ) 1

/-- The kernel is precisely the subgroup written in Example I.3.13(b):
the valuation exponent is arbitrary, while the unit is congruent to one
modulo `p^r`. -/
theorem padic_artin_one
    (p r : ℕ) [Fact p.Prime] [NeZero (p ^ r)]
    (L : Type*) [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    (u : ℤ_[p]ˣ) (m : ℤ) :
    padicCyclotomicArtin p r L
        ((((padicValuationInt p).symm u :
            (Padic.mulValuation (p := p)).valuationSubring.unitGroup) :
            ℚ_[p]ˣ) *
          (Units.mk0 (p : ℚ_[p]) (padic_prime_uniformizer p).ne_zero) ^ m) = 1 ↔
      (u : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ r} := by
  rw [padic_artin_zpow]
  exact padic_cyclotomic_action p r
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ r))) u

end

end Submission.CField.RExist
