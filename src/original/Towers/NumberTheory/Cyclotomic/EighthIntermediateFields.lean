import Mathlib
import Towers.NumberTheory.Fields.PowerMinusTwo

/-!
# Milne, Algebraic Number Theory, two-hour examination, Question 3

The Galois group of the eighth cyclotomic field is the Klein four group
`(ZMod 8)ˣ`.  Consequently its quadratic intermediate fields correspond to
the three index-two subgroups of `(ZMod 8)ˣ`.
-/

namespace Towers.NumberTheory.Milne

open IntermediateField Polynomial

section KleinFour

variable {G : Type*} [Group G]

private theorem index_two_card
    (hcard : Nat.card G = 4) (H : Subgroup G) (hH : H.index = 2) :
    Nat.card H = 2 := by
  have hmul := H.card_mul_index
  rw [hH, hcard] at hmul
  omega

private theorem zpowers_index_two
    (hcard : Nat.card G = 4) {x : G} (hxpow : x ^ 2 = 1) (hx : x ≠ 1) :
    (Subgroup.zpowers x).index = 2 := by
  have hord : orderOf x = 2 := orderOf_eq_prime hxpow hx
  have hzp : Nat.card (Subgroup.zpowers x) = 2 := by
    simpa [Nat.card_zpowers] using hord
  have hmul := (Subgroup.zpowers x).card_mul_index
  rw [hzp, hcard] at hmul
  omega

private theorem subgroups_klein_four
    [Finite G] (hcard : Nat.card G = 4) (hpow : ∀ x : G, x ^ 2 = 1) :
    Nat.card {H : Subgroup G // H.index = 2} = 3 := by
  classical
  let f : {x : G // x ≠ 1} → {H : Subgroup G // H.index = 2} := fun x =>
    ⟨Subgroup.zpowers x, zpowers_index_two hcard (hpow x) x.2⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy
    have hsub : Subgroup.zpowers (x : G) = Subgroup.zpowers (y : G) :=
      congrArg Subtype.val hxy
    let H := Subgroup.zpowers (x : G)
    have hHcard : Nat.card H = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (hpow x) x.2]
    have hxH : (x : G) ∈ H := Subgroup.mem_zpowers (x : G)
    have hyH : (y : G) ∈ H := by
      change (y : G) ∈ Subgroup.zpowers (x : G)
      rw [hsub]
      exact Subgroup.mem_zpowers (y : G)
    let xH : H := ⟨x, hxH⟩
    let yH : H := ⟨y, hyH⟩
    have hxH_ne : xH ≠ 1 := by
      intro hx
      exact x.2 (congrArg Subtype.val hx)
    have hyH_ne : yH ≠ 1 := by
      intro hy
      exact y.2 (congrArg Subtype.val hy)
    have hxyG : (x : G) = (y : G) := congrArg (fun z : H => (z : G)) <|
      ((Classical.choose_spec ((Nat.card_eq_two_iff' (1 : H)).mp hHcard)).2 xH hxH_ne).trans
        ((Classical.choose_spec ((Nat.card_eq_two_iff' (1 : H)).mp hHcard)).2 yH hyH_ne).symm
    exact Subtype.ext hxyG
  have hf_surjective : Function.Surjective f := by
    intro H
    have hHcard : Nat.card H.1 = 2 := index_two_card hcard H.1 H.2
    obtain ⟨x, hxne, _hxuniq⟩ := (Nat.card_eq_two_iff' (1 : H.1)).mp hHcard
    let xG : {x : G // x ≠ 1} := ⟨x, fun hx => hxne (Subtype.ext hx)⟩
    refine ⟨xG, Subtype.ext ?_⟩
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr x.2)
    rw [Nat.card_zpowers, orderOf_eq_prime (hpow x) xG.2, hHcard]
  let e := Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  rw [← Nat.card_congr e]
  letI := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hcard' : Fintype.card G = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  simp [hcard']

end KleinFour

private theorem z_eight_card : Nat.card (ZMod 8)ˣ = 4 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

private theorem units_z_eight (x : (ZMod 8)ˣ) : x ^ 2 = 1 := by
  classical
  fin_cases x <;> decide

private theorem z_eight_subgroups :
    Nat.card {H : Subgroup (ZMod 8)ˣ // H.index = 2} = 3 :=
  subgroups_klein_four z_eight_card units_z_eight

/-- The eighth cyclotomic field has exactly three quadratic intermediate fields. -/
theorem eight_intermediate_fields :
    Nat.card {E : IntermediateField ℚ (CyclotomicField 8 ℚ) //
      Module.finrank ℚ E = 2} = 3 := by
  let K := CyclotomicField 8 ℚ
  letI : IsCyclotomicExtension {8} ℚ K :=
    CyclotomicField.isCyclotomicExtension 8 ℚ
  letI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {8} ℚ K
  let gal : Gal(K / ℚ) ≃* (ZMod 8)ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod 8 K
  let galoisCorrespondence : IntermediateField ℚ K ≃ Subgroup (Gal(K / ℚ)) :=
    { toFun := fun (E : IntermediateField ℚ K) => IntermediateField.fixingSubgroup E
      invFun := fun (H : Subgroup (Gal(K / ℚ))) => IntermediateField.fixedField H
      left_inv := fun E => IsGalois.fixedField_fixingSubgroup E
      right_inv := fun H => IntermediateField.fixingSubgroup_fixedField H }
  let quadraticCorrespondence :
      {E : IntermediateField ℚ K // Module.finrank ℚ E = 2} ≃
        {H : Subgroup (Gal(K / ℚ)) // H.index = 2} :=
    galoisCorrespondence.subtypeEquiv fun E => by
      rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := E)]
      rfl
  have hgalcard : Nat.card Gal(K / ℚ) = 4 := by
    rw [Nat.card_congr gal.toEquiv]
    exact z_eight_card
  have hgalpow : ∀ σ : Gal(K / ℚ), σ ^ 2 = 1 := by
    intro σ
    apply gal.injective
    simp [units_z_eight]
  rw [Nat.card_congr quadraticCorrespondence]
  exact subgroups_klein_four hgalcard hgalpow

noncomputable section

local instance examinationThree_isCyclotomicExtension :
    IsCyclotomicExtension {8} ℚ (CyclotomicField 8 ℚ) :=
  CyclotomicField.isCyclotomicExtension 8 ℚ

/-- A fixed primitive eighth root of unity in the eighth cyclotomic field. -/
abbrev examinationThreeZeta : CyclotomicField 8 ℚ :=
  IsCyclotomicExtension.zeta 8 ℚ (CyclotomicField 8 ℚ)

private theorem examination_zeta_spec :
    IsPrimitiveRoot examinationThreeZeta 8 :=
  IsCyclotomicExtension.zeta_spec 8 ℚ (CyclotomicField 8 ℚ)

private theorem examination_zeta_ne : examinationThreeZeta ≠ 0 :=
  (examination_zeta_spec.isUnit (by norm_num)).ne_zero

private theorem examination_zeta_four : examinationThreeZeta ^ 4 = -1 := by
  apply IsPrimitiveRoot.eq_neg_one_of_two_right
  exact examination_zeta_spec.pow_of_dvd (by norm_num) (by norm_num)

/-- The element `ζ²` is a square root of `-1`. -/
theorem examination_three_zeta : (examinationThreeZeta ^ 2) ^ 2 = -1 := by
  rw [← pow_mul, examination_zeta_four]

/-- The element `ζ + ζ⁻¹` is a square root of `2`. -/
theorem examination_zeta_inv :
    (examinationThreeZeta + examinationThreeZeta⁻¹) ^ 2 = 2 := by
  field_simp [examination_zeta_ne]
  calc
    (examinationThreeZeta ^ 2 + 1) ^ 2 =
        examinationThreeZeta ^ 4 + 2 * examinationThreeZeta ^ 2 + 1 := by ring
    _ = examinationThreeZeta ^ 2 * 2 := by
      rw [examination_zeta_four]
      ring

/-- The element `ζ - ζ⁻¹` is a square root of `-2`. -/
theorem examination_sq_zeta :
    (examinationThreeZeta - examinationThreeZeta⁻¹) ^ 2 = -2 := by
  field_simp [examination_zeta_ne]
  calc
    (examinationThreeZeta ^ 2 - 1) ^ 2 =
        examinationThreeZeta ^ 4 - 2 * examinationThreeZeta ^ 2 + 1 := by ring
    _ = -(examinationThreeZeta ^ 2 * 2) := by
      rw [examination_zeta_four]
      ring

/-- The copy of `Q(i)` inside the eighth cyclotomic field. -/
abbrev examinationGaussianSubfield :
    IntermediateField ℚ (CyclotomicField 8 ℚ) :=
  ℚ⟮examinationThreeZeta ^ 2⟯

/-- The copy of `Q(sqrt 2)` inside the eighth cyclotomic field. -/
abbrev examinationTwoSubfield :
    IntermediateField ℚ (CyclotomicField 8 ℚ) :=
  ℚ⟮examinationThreeZeta + examinationThreeZeta⁻¹⟯

/-- The copy of `Q(sqrt (-2))` inside the eighth cyclotomic field. -/
abbrev examinationSqrtSubfield :
    IntermediateField ℚ (CyclotomicField 8 ℚ) :=
  ℚ⟮examinationThreeZeta - examinationThreeZeta⁻¹⟯

theorem examination_gaussian_subfield :
    Module.finrank ℚ examinationGaussianSubfield = 2 := by
  have hroot : IsPrimitiveRoot (examinationThreeZeta ^ 2) 4 :=
    examination_zeta_spec.pow_of_dvd (by norm_num) (by norm_num)
  have hmin := hroot.minpoly_eq_cyclotomic_of_irreducible
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 4))
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral
    (R := ℚ) (examinationThreeZeta ^ 2)), ← hmin, Polynomial.natDegree_cyclotomic]
  decide

theorem examination_sqrt_subfield :
    Module.finrank ℚ examinationTwoSubfield = 2 := by
  let x := examinationThreeZeta + examinationThreeZeta⁻¹
  have hx : x ^ 2 = algebraMap ℚ (CyclotomicField 8 ℚ) 2 :=
    examination_zeta_inv
  have hmin := minpoly_x_two (K := CyclotomicField 8 ℚ)
    (n := 2) (by norm_num) hx
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := ℚ) x),
    hmin, Polynomial.natDegree_X_pow_sub_C]

private theorem x_sq_eisenstein :
    (Polynomial.X ^ 2 - Polynomial.C (-2 : ℤ)).IsEisensteinAt
      (Ideal.span {(2 : ℤ)}) := by
  have hp : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
      (Nat.prime_iff_prime_int.mp Nat.prime_two)
  refine (monic_X_pow_sub_C (-2 : ℤ) (by norm_num)).isEisensteinAt_of_mem_of_notMem ?_ ?_ ?_
  · exact hp.ne_top
  · intro i hi
    rw [natDegree_X_pow_sub_C] at hi
    rw [coeff_sub, coeff_X_pow, coeff_C]
    by_cases hi0 : i = 0
    · subst i
      simp
    · have hi2 : i ≠ 2 := Nat.ne_of_lt hi
      rw [if_neg hi2, if_neg hi0, sub_zero]
      exact Ideal.zero_mem _
  · rw [coeff_zero_eq_eval_zero, eval_sub, eval_pow, eval_X, eval_C,
      zero_pow (by norm_num), zero_sub, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    norm_num

private theorem irreducible_sq_rat :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (2 : ℚ)) := by
  have h := eisenstein_irreducible_fraction (A := ℤ) (K := ℚ)
    ((Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr
      (Nat.prime_iff_prime_int.mp Nat.prime_two))
    x_sq_eisenstein
    (monic_X_pow_sub_C (-2 : ℤ) (by norm_num))
    (by rw [natDegree_X_pow_sub_C]; norm_num)
  simpa using h

theorem examination_subfield_finrank :
    Module.finrank ℚ examinationSqrtSubfield = 2 := by
  let x := examinationThreeZeta - examinationThreeZeta⁻¹
  have hx : x ^ 2 = algebraMap ℚ (CyclotomicField 8 ℚ) (-2) :=
    by
      simpa [x] using examination_sq_zeta
  have heval : aeval x (X ^ 2 + C (2 : ℚ)) = 0 := by
    simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 + C (2 : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic irreducible_sq_rat heval
      (monic_X_pow_add_C 2 (by norm_num))).symm
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := ℚ) x),
    hmin]
  norm_num

private noncomputable abbrev examinationSigmaFive :
    Gal(CyclotomicField 8 ℚ / ℚ) :=
  (IsCyclotomicExtension.Rat.galEquivZMod 8 (CyclotomicField 8 ℚ)).symm
    (ZMod.unitOfCoprime 5 (by norm_num))

private noncomputable abbrev examinationSigmaSeven :
    Gal(CyclotomicField 8 ℚ / ℚ) :=
  (IsCyclotomicExtension.Rat.galEquivZMod 8 (CyclotomicField 8 ℚ)).symm
    (ZMod.unitOfCoprime 7 (by norm_num))

private theorem examination_sigma_zeta :
    examinationSigmaFive examinationThreeZeta = examinationThreeZeta ^ 5 := by
  let gal := IsCyclotomicExtension.Rat.galEquivZMod 8 (CyclotomicField 8 ℚ)
  calc
    examinationSigmaFive examinationThreeZeta =
        examinationThreeZeta ^ (gal examinationSigmaFive).val.val :=
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq 8
        (CyclotomicField 8 ℚ) examinationSigmaFive examination_zeta_spec.pow_eq_one
    _ = examinationThreeZeta ^ 5 := by
      rw [show gal examinationSigmaFive = ZMod.unitOfCoprime 5 (by norm_num) by
        exact gal.apply_symm_apply _]
      congr 1

private theorem sigma_seven_zeta :
    examinationSigmaSeven examinationThreeZeta = examinationThreeZeta ^ 7 := by
  let gal := IsCyclotomicExtension.Rat.galEquivZMod 8 (CyclotomicField 8 ℚ)
  calc
    examinationSigmaSeven examinationThreeZeta =
        examinationThreeZeta ^ (gal examinationSigmaSeven).val.val :=
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq 8
        (CyclotomicField 8 ℚ) examinationSigmaSeven examination_zeta_spec.pow_eq_one
    _ = examinationThreeZeta ^ 7 := by
      rw [show gal examinationSigmaSeven = ZMod.unitOfCoprime 7 (by norm_num) by
        exact gal.apply_symm_apply _]
      congr 1

private theorem examination_sigma_sq :
    examinationSigmaFive (examinationThreeZeta ^ 2) = examinationThreeZeta ^ 2 := by
  rw [map_pow, examination_sigma_zeta, ← pow_mul]
  calc
    examinationThreeZeta ^ (5 * 2) = examinationThreeZeta ^ 8 * examinationThreeZeta ^ 2 := by
      ring
    _ = examinationThreeZeta ^ 2 := by rw [examination_zeta_spec.pow_eq_one, one_mul]

private theorem examination_sigma_two :
    examinationSigmaFive (examinationThreeZeta + examinationThreeZeta⁻¹) =
      -(examinationThreeZeta + examinationThreeZeta⁻¹) := by
  rw [map_add, map_inv₀, examination_sigma_zeta]
  field_simp [examination_zeta_ne]
  have h10 : examinationThreeZeta ^ 10 = examinationThreeZeta ^ 2 := by
    calc
      examinationThreeZeta ^ 10 = examinationThreeZeta ^ 8 * examinationThreeZeta ^ 2 := by ring
      _ = examinationThreeZeta ^ 2 := by rw [examination_zeta_spec.pow_eq_one, one_mul]
  rw [h10, examination_zeta_four]
  ring

private theorem examination_sigma_neg :
    examinationSigmaFive (examinationThreeZeta - examinationThreeZeta⁻¹) =
      -(examinationThreeZeta - examinationThreeZeta⁻¹) := by
  rw [map_sub, map_inv₀, examination_sigma_zeta]
  field_simp [examination_zeta_ne]
  have h10 : examinationThreeZeta ^ 10 = examinationThreeZeta ^ 2 := by
    calc
      examinationThreeZeta ^ 10 = examinationThreeZeta ^ 8 * examinationThreeZeta ^ 2 := by ring
      _ = examinationThreeZeta ^ 2 := by rw [examination_zeta_spec.pow_eq_one, one_mul]
  rw [h10, examination_zeta_four]
  ring

private theorem sigma_seven_two :
    examinationSigmaSeven (examinationThreeZeta + examinationThreeZeta⁻¹) =
      examinationThreeZeta + examinationThreeZeta⁻¹ := by
  rw [map_add, map_inv₀, sigma_seven_zeta]
  field_simp [examination_zeta_ne]
  have h14 : examinationThreeZeta ^ 14 = examinationThreeZeta ^ 6 := by
    calc
      examinationThreeZeta ^ 14 = examinationThreeZeta ^ 8 * examinationThreeZeta ^ 6 := by ring
      _ = examinationThreeZeta ^ 6 := by rw [examination_zeta_spec.pow_eq_one, one_mul]
  calc
    examinationThreeZeta ^ 14 + 1 = examinationThreeZeta ^ 6 + 1 := by rw [h14]
    _ = examinationThreeZeta ^ 6 * (examinationThreeZeta ^ 2 + 1) := by
      rw [show examinationThreeZeta ^ 6 * (examinationThreeZeta ^ 2 + 1) =
        examinationThreeZeta ^ 8 + examinationThreeZeta ^ 6 by ring,
        examination_zeta_spec.pow_eq_one]
      ring

private theorem sigma_seven_neg :
    examinationSigmaSeven (examinationThreeZeta - examinationThreeZeta⁻¹) =
      -(examinationThreeZeta - examinationThreeZeta⁻¹) := by
  rw [map_sub, map_inv₀, sigma_seven_zeta]
  field_simp [examination_zeta_ne]
  have h14 : examinationThreeZeta ^ 14 = examinationThreeZeta ^ 6 := by
    calc
      examinationThreeZeta ^ 14 = examinationThreeZeta ^ 8 * examinationThreeZeta ^ 6 := by ring
      _ = examinationThreeZeta ^ 6 := by rw [examination_zeta_spec.pow_eq_one, one_mul]
  calc
    examinationThreeZeta ^ 14 - 1 = examinationThreeZeta ^ 6 - 1 := by rw [h14]
    _ = -(examinationThreeZeta ^ 6 * (examinationThreeZeta ^ 2 - 1)) := by
      rw [show examinationThreeZeta ^ 6 * (examinationThreeZeta ^ 2 - 1) =
        examinationThreeZeta ^ 8 - examinationThreeZeta ^ 6 by ring,
        examination_zeta_spec.pow_eq_one]
      ring

private theorem examination_sqrt_zero :
    examinationThreeZeta + examinationThreeZeta⁻¹ ≠ 0 := by
  intro h
  have hs := examination_zeta_inv
  rw [h] at hs
  norm_num at hs

private theorem examination_sqrt_ne :
    examinationThreeZeta - examinationThreeZeta⁻¹ ≠ 0 := by
  intro h
  have hs := examination_sq_zeta
  rw [h] at hs
  norm_num at hs

private theorem examination_sigma_gaussian :
    examinationSigmaFive ∈ examinationGaussianSubfield.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  change ∀ x ∈ ℚ⟮examinationThreeZeta ^ 2⟯, examinationSigmaFive • x = x
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  simpa using examination_sigma_sq

private theorem examination_sigma_sqrt :
    examinationSigmaFive ∉ examinationTwoSubfield.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  change ¬∀ x ∈ ℚ⟮examinationThreeZeta + examinationThreeZeta⁻¹⟯,
    examinationSigmaFive • x = x
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  change examinationSigmaFive
      (examinationThreeZeta + examinationThreeZeta⁻¹) ≠
        examinationThreeZeta + examinationThreeZeta⁻¹
  rw [examination_sigma_two, ne_eq,
    CharZero.neg_eq_self_iff]
  exact examination_sqrt_zero

private theorem examination_sigma_five :
    examinationSigmaFive ∉ examinationSqrtSubfield.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  change ¬∀ x ∈ ℚ⟮examinationThreeZeta - examinationThreeZeta⁻¹⟯,
    examinationSigmaFive • x = x
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  change examinationSigmaFive
      (examinationThreeZeta - examinationThreeZeta⁻¹) ≠
        examinationThreeZeta - examinationThreeZeta⁻¹
  rw [examination_sigma_neg, ne_eq,
    CharZero.neg_eq_self_iff]
  exact examination_sqrt_ne

private theorem sigma_seven_sqrt :
    examinationSigmaSeven ∈ examinationTwoSubfield.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  change ∀ x ∈ ℚ⟮examinationThreeZeta + examinationThreeZeta⁻¹⟯,
    examinationSigmaSeven • x = x
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  simpa using sigma_seven_two

private theorem examination_sigma_seven :
    examinationSigmaSeven ∉ examinationSqrtSubfield.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  change ¬∀ x ∈ ℚ⟮examinationThreeZeta - examinationThreeZeta⁻¹⟯,
    examinationSigmaSeven • x = x
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  change examinationSigmaSeven
      (examinationThreeZeta - examinationThreeZeta⁻¹) ≠
        examinationThreeZeta - examinationThreeZeta⁻¹
  rw [sigma_seven_neg, ne_eq,
    CharZero.neg_eq_self_iff]
  exact examination_sqrt_ne

theorem examination_gaussian_ne :
    examinationGaussianSubfield ≠ examinationTwoSubfield := by
  intro h
  apply examination_sigma_sqrt
  rw [← h]
  exact examination_sigma_gaussian

theorem examination_gaussian_sqrt :
    examinationGaussianSubfield ≠ examinationSqrtSubfield := by
  intro h
  apply examination_sigma_five
  rw [← h]
  exact examination_sigma_gaussian

theorem examination_sqrt_neg :
    examinationTwoSubfield ≠ examinationSqrtSubfield := by
  intro h
  apply examination_sigma_seven
  rw [← h]
  exact sigma_seven_sqrt

/-- Examination 3: every quadratic subfield of `Q(ζ₈)` is one of
`Q(i)`, `Q(sqrt 2)`, or `Q(sqrt (-2))`. -/
theorem examin_quadr_inter
    (E : IntermediateField ℚ (CyclotomicField 8 ℚ))
    (hE : Module.finrank ℚ E = 2) :
    E = examinationGaussianSubfield ∨
      E = examinationTwoSubfield ∨
      E = examinationSqrtSubfield := by
  classical
  let Q := {F : IntermediateField ℚ (CyclotomicField 8 ℚ) //
    Module.finrank ℚ F = 2}
  let a : Q := ⟨examinationGaussianSubfield,
    examination_gaussian_subfield⟩
  let b : Q := ⟨examinationTwoSubfield,
    examination_sqrt_subfield⟩
  let c : Q := ⟨examinationSqrtSubfield,
    examination_subfield_finrank⟩
  let q : Q := ⟨E, hE⟩
  have hcardQ : Nat.card Q = 3 := eight_intermediate_fields
  letI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcardQ]; norm_num)
  letI := Fintype.ofFinite Q
  by_contra h
  push Not at h
  have hab : a ≠ b := by
    intro e
    exact examination_gaussian_ne (congrArg Subtype.val e)
  have hac : a ≠ c := by
    intro e
    exact examination_gaussian_sqrt (congrArg Subtype.val e)
  have hbc : b ≠ c := by
    intro e
    exact examination_sqrt_neg (congrArg Subtype.val e)
  have hqa : q ≠ a := by
    intro e
    exact h.1 (congrArg Subtype.val e)
  have hqb : q ≠ b := by
    intro e
    exact h.2.1 (congrArg Subtype.val e)
  have hqc : q ≠ c := by
    intro e
    exact h.2.2 (congrArg Subtype.val e)
  have hfour : ({a, b, c, q} : Finset Q).card = 4 := by
    simp [hab, hac, hbc, Ne.symm hqa, Ne.symm hqb, Ne.symm hqc]
  have hle := Finset.card_le_univ ({a, b, c, q} : Finset Q)
  have hFcard : Fintype.card Q = 3 := by
    simpa [Nat.card_eq_fintype_card] using hcardQ
  rw [hfour, hFcard] at hle
  omega

end

end Towers.NumberTheory.Milne
