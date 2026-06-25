import Submission.ClassField.HigherReciprocity.PowerResidue
import Submission.NumberTheory.Locals.CompleteDVRHenselian
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Chapter VIII, Statement 5.2: the Hensel step

For a unit in a complete discretely valued field, being an `n`th power in
the residue field is equivalent to being an `n`th power in the field,
provided the residue characteristic does not divide `n`.  This is the
equivalence `(b) ↔ (c)` in Statement VIII.5.2.
-/

namespace Submission.CField.HRecip

open IsLocalRing Polynomial
open Submission.NumberTheory.Milne
open scoped NormedField Valued

noncomputable section

/-- The Hensel part of Statement VIII.5.2 at the level of a Henselian local
ring.  The hypotheses say exactly that `a` is a local unit and that the
residue characteristic does not divide `n`. -/
theorem henselian_residue_power
    {A : Type*} [CommRing A] [HenselianLocalRing A]
    {n : ℕ} (hn : (n : ResidueField A) ≠ 0) (a : Aˣ) :
    (∃ y : ResidueField A, y ^ n = residue A (a : A)) ↔
      ∃ x : A, x ^ n = (a : A) := by
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  constructor
  · rintro ⟨y, hy⟩
    let f : A[X] := X ^ n - C (a : A)
    have hf : f.Monic := by
      simpa [f] using monic_X_pow_sub_C (a : A) hn0
    have ha0 : residue A (a : A) ≠ 0 := by
      exact (Units.map (residue A).toMonoidHom a).ne_zero
    have hy0 : y ≠ 0 := by
      intro hyzero
      apply ha0
      rw [← hy, hyzero, zero_pow hn0]
    have hroot : aeval y f = 0 := by
      simp only [f, map_sub, map_pow, aeval_X, aeval_C]
      exact sub_eq_zero.mpr hy
    have hsimple : aeval y (derivative f) ≠ 0 := by
      simpa [f, derivative_sub, derivative_X_pow] using
        mul_ne_zero hn (pow_ne_zero (n - 1) hy0)
    have hlift :=
      ((HenselianLocalRing.TFAE A).out 0 1).mp
        (inferInstance : HenselianLocalRing A)
    obtain ⟨x, hx, _⟩ := hlift f hf y hroot hsimple
    refine ⟨x, ?_⟩
    apply sub_eq_zero.mp
    simpa [f, Polynomial.IsRoot.def] using hx
  · rintro ⟨x, hx⟩
    refine ⟨residue A x, ?_⟩
    simpa using congrArg (residue A) hx

/-- Statement VIII.5.2 `(b) ↔ (c)` for a complete discretely valued
field.  A field root in the reverse direction is automa integral:
its norm has `n`th power one because `a` is a unit. -/
theorem complete_dvr_power
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsDiscreteValuationRing (Valued.integer K)]
    {n : ℕ} (hn : (n : ResidueField (Valued.integer K)) ≠ 0)
    (a : (Valued.integer K)ˣ) :
    (∃ y : ResidueField (Valued.integer K),
        y ^ n = residue (Valued.integer K) (a : Valued.integer K)) ↔
      ∃ x : K, x ^ n = ((a : Valued.integer K) : K) := by
  letI : HenselianLocalRing (Valued.integer K) :=
    valued_henselian_ring K
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  constructor
  · intro h
    obtain ⟨x, hx⟩ :=
      (henselian_residue_power hn a).mp h
    refine ⟨(x : K), ?_⟩
    exact congrArg Subtype.val hx
  · rintro ⟨x, hx⟩
    have hxnorm : ‖x‖ = 1 := by
      apply (pow_eq_one_iff_of_nonneg (norm_nonneg x) hn0).mp
      rw [← norm_pow, hx, Valued.integer.norm_coe_unit]
    let x₀ : Valued.integer K :=
      ⟨x, Valued.integer.mem_iff.mpr hxnorm.le⟩
    have hx₀ : x₀ ^ n = (a : Valued.integer K) := by
      apply Subtype.ext
      exact hx
    exact (henselian_residue_power hn a).mpr ⟨x₀, hx₀⟩

/-- **Statement VIII.5.2, complete-DVR form.**  The power residue symbol of
a local unit is one if and only if that unit is an `n`th power in the
completed field.  The divisibility hypothesis is the finite-field fact
`n ∣ q - 1`; the nonvanishing hypothesis says that the residue
characteristic does not divide `n`. -/
theorem complete_dvr_residue
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsDiscreteValuationRing (Valued.integer K)]
    [Finite (ResidueField (Valued.integer K))]
    {n : ℕ}
    (hcard : n ∣ Nat.card (ResidueField (Valued.integer K)) - 1)
    (hn : (n : ResidueField (Valued.integer K)) ≠ 0)
    (a : (Valued.integer K)ˣ) :
    powerResidueValue n
        (Units.map (residue (Valued.integer K)).toMonoidHom a) = 1 ↔
      ∃ x : K, x ^ n = ((a : Valued.integer K) : K) := by
  let R := Valued.integer K
  let k := ResidueField R
  let abar : kˣ := Units.map (residue R).toMonoidHom a
  have habar0 : (abar : k) ≠ 0 := abar.ne_zero
  constructor
  · intro hsymbol
    have hresidueUnit : ∃ y : kˣ, y ^ n = abar :=
      (field_residue_one hcard abar).mp hsymbol
    obtain ⟨y, hy⟩ := hresidueUnit
    apply (complete_dvr_power hn a).mp
    refine ⟨(y : k), ?_⟩
    exact congrArg Units.val hy
  · intro hfield
    obtain ⟨y, hy⟩ :=
      (complete_dvr_power hn a).mpr hfield
    have hy0 : y ≠ 0 := by
      intro hzero
      apply habar0
      change residue R (a : R) = 0
      rw [← hy, hzero, zero_pow]
      intro hn0
      subst n
      simp at hn
    let yu : kˣ := Units.mk0 y hy0
    apply (field_residue_one hcard abar).mpr
    refine ⟨yu, ?_⟩
    apply Units.ext
    exact hy

/-- The preceding source statement with `n ∣ q - 1` derived from the
primitive `n`th root of unity supplied by the standing hypothesis of
Section VIII.5.  Thus the only remaining arithmetic condition is precisely
`𝔭 ∉ S(a)`: the residue characteristic does not divide `n`. -/
theorem complete_dvr_primitive
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsDiscreteValuationRing (Valued.integer K)]
    [Finite (ResidueField (Valued.integer K))]
    {n : ℕ} (zeta : ResidueField (Valued.integer K))
    (hzeta : IsPrimitiveRoot zeta n)
    (hn : (n : ResidueField (Valued.integer K)) ≠ 0)
    (a : (Valued.integer K)ˣ) :
    powerResidueValue n
        (Units.map (residue (Valued.integer K)).toMonoidHom a) = 1 ↔
      ∃ x : K, x ^ n = ((a : Valued.integer K) : K) := by
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  let zetaUnit : (ResidueField (Valued.integer K))ˣ :=
    (hzeta.isUnit hn0).unit
  have hzetaUnit : IsPrimitiveRoot zetaUnit n :=
    hzeta.isUnit_unit hn0
  have hcard : n ∣ Nat.card (ResidueField (Valued.integer K)) - 1 := by
    have hdiv : n ∣ Nat.card (ResidueField (Valued.integer K))ˣ := by
      rw [hzetaUnit.eq_orderOf]
      exact orderOf_dvd_natCard zetaUnit
    simpa only [Nat.card_units] using hdiv
  exact complete_dvr_residue hcard hn a

end

end Submission.CField.HRecip
