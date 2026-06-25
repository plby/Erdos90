import Towers.ClassField.CyclotomicBrauer.Cyclotomic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

/-!
# Lemma VII.7.3: total complexity of normal number fields

A Galois number field is either totally real or totally complex.  This
small normality lemma is the archimedean input for the diagonal two-primary
fixed field used in Lemma VII.7.3.
-/

namespace Towers.CField.CBrauer

open NumberField

noncomputable section

/-- A Galois number field over `ℚ` which is not totally real is totally
complex.  Normality makes every complex embedding differ from a chosen one
by a field automorphism, so the existence of one real place would force all
places to be real. -/
theorem totally_complex_real
    (E : Type*) [Field E] [NumberField E] [IsGalois ℚ E]
    (hnotReal : ¬ NumberField.IsTotallyReal E) :
    NumberField.IsTotallyComplex E := by
  rw [NumberField.isTotallyComplex_iff]
  intro w
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hwReal
  apply hnotReal
  rw [NumberField.isTotallyReal_iff]
  intro v
  rw [NumberField.InfinitePlace.isReal_iff]
  have hwEmbeddingReal : NumberField.ComplexEmbedding.IsReal w.embedding :=
    NumberField.InfinitePlace.isReal_iff.mp hwReal
  have hagree :
      w.embedding.comp (algebraMap ℚ E) =
        v.embedding.comp (algebraMap ℚ E) :=
    Subsingleton.elim _ _
  obtain ⟨sigma, hsigma⟩ :=
    NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq
      w.embedding v.embedding hagree
  rw [← hsigma]
  exact hwEmbeddingReal.comp sigma.symm.toRingHom

/-- In a rational cyclotomic field, the automorphism corresponding to
`-1 ∈ (ZMod n)ˣ` fixes every totally real intermediate field.  This is
the precise link between complex conjugation and the subgroup test used for
the diagonal two-primary fixed field. -/
theorem fixing_totally_real
    (n : ℕ) [NeZero n]
    (C : Type*) [Field C] [NumberField C]
    [IsCyclotomicExtension {n} ℚ C]
    (E : IntermediateField ℚ C)
    [NumberField E] [NumberField.IsTotallyReal E] :
    (IsCyclotomicExtension.Rat.galEquivZMod n C).symm
        (-1 : (ZMod n)ˣ) ∈ E.fixingSubgroup := by
  let zeta : C := IsCyclotomicExtension.zeta n ℚ C
  have hzeta : IsPrimitiveRoot zeta n :=
    IsCyclotomicExtension.zeta_spec n ℚ C
  let sigma : Gal(C/ℚ) :=
    (IsCyclotomicExtension.Rat.galEquivZMod n C).symm
      (-1 : (ZMod n)ˣ)
  let phi : C →+* ℂ :=
    NumberField.ComplexEmbedding.lift C (algebraMap ℚ ℂ)
  have hphiZeta : IsPrimitiveRoot (phi zeta) n :=
    hzeta.map_of_injective phi.injective
  have hpowNeg :
      (phi zeta) ^ ((-1 : (ZMod n)ˣ).val.val) = (phi zeta)⁻¹ := by
    have hmod : ((-1 : (ZMod n)ˣ).val.val) ≡ n - 1 [MOD n] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      rw [Nat.cast_sub (NeZero.pos n)]
      simp
    have hpowPred : (phi zeta) ^ (n - 1) = (phi zeta)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (NeZero.pos n)]
      exact hphiZeta.pow_eq_one
    exact ((hphiZeta.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.mpr
      (hphiZeta.eq_orderOf.symm ▸ hmod)).trans hpowPred
  have hsigmaZeta : sigma zeta =
      zeta ^ ((-1 : (ZMod n)ˣ).val.val) := by
    have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      n C sigma hzeta.pow_eq_one
    simpa only [sigma, MulEquiv.apply_symm_apply] using h
  have hconjugation :
      phi.comp sigma.toRingHom = NumberField.ComplexEmbedding.conjugate phi := by
    apply RingHom.equivRatAlgHom.injective
    apply (hzeta.powerBasis ℚ).algHom_ext
    change phi (sigma zeta) = star (phi zeta)
    rw [hsigmaZeta, map_pow, hpowNeg]
    exact Complex.inv_eq_conj
      (Complex.norm_eq_one_of_pow_eq_one hphiZeta.pow_eq_one (NeZero.ne n))
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  apply phi.injective
  let phiE : E →+* ℂ := phi.comp E.val
  have hphiEReal : NumberField.ComplexEmbedding.IsReal phiE :=
    NumberField.IsTotallyReal.complexEmbedding_isReal phiE
  calc
    phi (sigma x) = star (phi x) := by
      exact RingHom.congr_fun hconjugation x
    _ = phi x := by
      have hrealEq := NumberField.ComplexEmbedding.isReal_iff.mp hphiEReal
      exact RingHom.congr_fun hrealEq ⟨x, hx⟩

/-- A normal fixed field in a rational cyclotomic extension is totally
complex when its defining subgroup does not contain complex conjugation. -/
theorem totally_complex_not
    (n : ℕ) [NeZero n]
    (C : Type*) [Field C] [NumberField C]
    [IsCyclotomicExtension {n} ℚ C]
    (H : Subgroup Gal(C/ℚ)) [H.Normal]
    (hneg : (-1 : (ZMod n)ˣ) ∉
      H.map (IsCyclotomicExtension.Rat.galEquivZMod n C).toMonoidHom) :
    NumberField.IsTotallyComplex (IntermediateField.fixedField H) := by
  letI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {n} ℚ C
  let E : IntermediateField ℚ C := IntermediateField.fixedField H
  letI : IsGalois ℚ E := IsGalois.of_fixedField_normal_subgroup H
  letI : NumberField E := NumberField.of_module_finite ℚ E
  apply totally_complex_real E
  intro hreal
  letI : NumberField.IsTotallyReal E := hreal
  have hfix :=
    fixing_totally_real n C E
  have hmemH :
      (IsCyclotomicExtension.Rat.galEquivZMod n C).symm
          (-1 : (ZMod n)ˣ) ∈ H := by
    simpa only [E, IntermediateField.fixingSubgroup_fixedField] using hfix
  apply hneg
  exact ⟨_, hmemH,
    (IsCyclotomicExtension.Rat.galEquivZMod n C).apply_symm_apply _⟩

end

end Towers.CField.CBrauer
