import Towers.FieldTheory.RationalFinitePlace
import Towers.NumberTheory.Splitting


open scoped Pointwise

noncomputable section

namespace Towers

open TBluepr

lemma scratch_integers_smul
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K ↥E] [IsGalois K ↥E]
    (σ : Gal(L/K))
    (x : NumberField.RingOfIntegers E) :
    σ • (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L) x) =
      algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L)
        ((σ.restrictNormalHom E) • x) := by
  apply Subtype.ext
  let y : NumberField.RingOfIntegers L :=
    algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L) x
  calc
    algebraMap (NumberField.RingOfIntegers L) L
        (σ • (algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L) x))
      = σ (algebraMap (NumberField.RingOfIntegers L) L y) := by
          exact
            (congrArg Subtype.val
              (alg_gal_restrict
                (K := K) (E := L) (σ := σ) (x := y))).trans
              (algebraMap_galRestrict_apply
                (A := NumberField.RingOfIntegers K) (K := K) (L := L)
                (B := NumberField.RingOfIntegers L) σ y)
    _ =
        σ (algebraMap E L (algebraMap (NumberField.RingOfIntegers E) E x)) := by
          rfl
    _ =
        algebraMap E L
          ((σ.restrictNormalHom E) (algebraMap (NumberField.RingOfIntegers E) E x)) := by
            simpa using
              (AlgEquiv.restrictNormalHom_apply
                (L := E) σ (algebraMap (NumberField.RingOfIntegers E) E x)).symm
    _ =
        algebraMap E L
          (algebraMap (NumberField.RingOfIntegers E) E
            ((σ.restrictNormalHom E) • x)) := by
              rfl
    _ =
        algebraMap (NumberField.RingOfIntegers L) L
          (algebraMap (NumberField.RingOfIntegers E)
            (NumberField.RingOfIntegers L)
            ((σ.restrictNormalHom E) • x)) := by
              rfl

lemma scratch_smul
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (E : IntermediateField K L) [FiniteDimensional K ↥E] [IsGalois K ↥E]
    (σ : Gal(L/K))
    (P : Ideal (NumberField.RingOfIntegers L)) :
    Ideal.under (NumberField.RingOfIntegers E) (σ • P) =
      (σ.restrictNormalHom E) • Ideal.under (NumberField.RingOfIntegers E) P := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  change
    (σ⁻¹ •
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L) x) ∈ P ↔
      algebraMap (NumberField.RingOfIntegers E)
        (NumberField.RingOfIntegers L)
        ((σ.restrictNormalHom E)⁻¹ • x) ∈ P
  have h :=
    scratch_integers_smul
      (E := E) (σ := σ⁻¹) (x := x)
  constructor <;> intro hx
  · have hx' :
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L)
          ((σ⁻¹).restrictNormalHom E • x) ∈ P := by
        exact h ▸ hx
    simpa using hx'
  · have hx' :
        algebraMap (NumberField.RingOfIntegers E)
          (NumberField.RingOfIntegers L)
          ((σ⁻¹).restrictNormalHom E • x) ∈ P := by
        simpa using hx
    exact h.symm ▸ hx'

lemma scratch_completely_fixing
    {L : Type*} [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (E : IntermediateField ℚ L) [FiniteDimensional ℚ ↥E] [IsGalois ℚ ↥E]
    {q : ℕ} (hq : Nat.Prime q)
    (P : Ideal (NumberField.RingOfIntegers L)) [P.IsPrime]
    [P.LiesOver (Ideal.rationalPrimeIdeal q)]
    (hPstab :
      MulAction.stabilizer (Gal(L/ℚ)) P ≤ E.fixingSubgroup) :
    splitsCompletely ↥E q := by
  letI : IsScalarTower ℤ ℚ ↥E := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    simp
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ ↥E (NumberField.RingOfIntegers E)
  letI : IsGaloisGroup Gal(↥E/ℚ) ℤ (NumberField.RingOfIntegers E) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(↥E/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers E) (K := ℚ) (L := ↥E)
  letI : IsGaloisGroup Gal(L/ℚ) ℤ (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := Gal(L/ℚ)) (A := ℤ)
      (B := NumberField.RingOfIntegers L) (K := ℚ) (L := L)
  letI : IsGaloisGroup E.fixingSubgroup ↥E L :=
    IsGaloisGroup.intermediateField (G := Gal(L/ℚ)) (K := ℚ) (L := L) (F := E)
  letI := IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers E) E L
    (NumberField.RingOfIntegers L)
  letI : IsGaloisGroup E.fixingSubgroup
      (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing (G := E.fixingSubgroup)
      (A := NumberField.RingOfIntegers E) (B := NumberField.RingOfIntegers L)
      (K := ↥E) (L := L)
  let qI : Ideal ℤ := Ideal.rationalPrimeIdeal q
  have hqI0 : qI ≠ ⊥ := rational_ne_bot hq
  letI : qI.IsMaximal := rational_ideal_maximal hq
  letI : Field (ℤ ⧸ qI) := Ideal.Quotient.field qI
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 P
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := P)
  letI : Field ((NumberField.RingOfIntegers L) ⧸ P) := Ideal.Quotient.field P
  letI : Algebra.IsSeparable (ℤ ⧸ qI) ((NumberField.RingOfIntegers L) ⧸ P) := by
    letI : IsGalois (ℤ ⧸ qI) ((NumberField.RingOfIntegers L) ⧸ P) :=
      { __ := Ideal.Quotient.normal (A := ℤ) (G := Gal(L/ℚ)) qI P }
    infer_instance
  let Q : Ideal (NumberField.RingOfIntegers E) := P.under (NumberField.RingOfIntegers E)
  letI : Q.LiesOver qI := by
    rw [Ideal.liesOver_iff]
    simpa [Q, Ideal.liesOver_iff] using (show P.LiesOver qI by infer_instance)
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqI0 Q
  letI : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (p := qI) (P := Q)
  letI : P.LiesOver Q := by
    simp [Q, Ideal.liesOver_iff]
  letI : Field ((NumberField.RingOfIntegers E) ⧸ Q) := Ideal.Quotient.field Q
  letI : Algebra.IsSeparable (ℤ ⧸ qI) ((NumberField.RingOfIntegers E) ⧸ Q) := by
    letI : IsGalois (ℤ ⧸ qI) ((NumberField.RingOfIntegers E) ⧸ Q) :=
      { __ := Ideal.Quotient.normal (A := ℤ) (G := Gal(↥E/ℚ)) qI Q }
    infer_instance
  let H : Subgroup (Gal(L/ℚ)) := MulAction.stabilizer (Gal(L/ℚ)) P
  have hHstab : H ≤ E.fixingSubgroup := by
    simpa [H] using hPstab
  have hHfull :
      Nat.card H =
        qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
          qI.inertiaDegIn (NumberField.RingOfIntegers L) := by
    simpa [H] using
      (Ideal.card_stabilizer_eq (G := Gal(L/ℚ)) qI hqI0 P)
  letI : Algebra.IsSeparable ((NumberField.RingOfIntegers E) ⧸ Q)
      ((NumberField.RingOfIntegers L) ⧸ P) := by
    letI : IsGalois ((NumberField.RingOfIntegers E) ⧸ Q)
        ((NumberField.RingOfIntegers L) ⧸ P) :=
      { __ := Ideal.Quotient.normal (A := NumberField.RingOfIntegers E)
          (G := E.fixingSubgroup) Q P }
    infer_instance
  have hHrel_eq :
      MulAction.stabilizer E.fixingSubgroup P = H.subgroupOf E.fixingSubgroup := by
    ext σ
    rfl
  have hHrel :
      Nat.card H =
        Q.ramificationIdxIn (NumberField.RingOfIntegers L) *
          Q.inertiaDegIn (NumberField.RingOfIntegers L) := by
    calc
      Nat.card H = Nat.card (H.subgroupOf E.fixingSubgroup) := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHstab).symm.toEquiv
      _ = Nat.card (MulAction.stabilizer E.fixingSubgroup P) := by
        rw [hHrel_eq]
      _ = Q.ramificationIdxIn (NumberField.RingOfIntegers L) *
            Q.inertiaDegIn (NumberField.RingOfIntegers L) := by
              simpa using
                (Ideal.card_stabilizer_eq (G := E.fixingSubgroup) Q hQ0 P)
  have hramMul :
      qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
          Q.ramificationIdxIn (NumberField.RingOfIntegers L) =
        qI.ramificationIdxIn (NumberField.RingOfIntegers L) := by
    simpa using
      (Ideal.ramificationIdxIn_mul_ramificationIdxIn'
        (p := qI) Q (Gal(↥E/ℚ)) (NumberField.RingOfIntegers L)
        (Gal(L/ℚ)) E.fixingSubgroup)
  have hinMul :
      qI.inertiaDegIn (NumberField.RingOfIntegers E) *
          Q.inertiaDegIn (NumberField.RingOfIntegers L) =
        qI.inertiaDegIn (NumberField.RingOfIntegers L) := by
    simpa using
      (Ideal.inertiaDegIn_mul_inertiaDegIn
        (p := qI) Q (Gal(↥E/ℚ)) (NumberField.RingOfIntegers L)
        (Gal(L/ℚ)) E.fixingSubgroup)
  have hQprod_ne_zero :
      Q.ramificationIdxIn (NumberField.RingOfIntegers L) *
          Q.inertiaDegIn (NumberField.RingOfIntegers L) ≠ 0 := by
    rw [← hHrel]
    letI : Finite H := inferInstance
    have hHnonempty : Nonempty ↥H := ⟨⟨1, by simp [H]⟩⟩
    exact Nat.pos_iff_ne_zero.mp <| Nat.card_pos_iff.mpr ⟨hHnonempty, inferInstance⟩
  have hmul :
      qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
          qI.inertiaDegIn (NumberField.RingOfIntegers E) = 1 := by
    let b :=
      Q.ramificationIdxIn (NumberField.RingOfIntegers L) *
        Q.inertiaDegIn (NumberField.RingOfIntegers L)
    have hb_ne_zero : b ≠ 0 := hQprod_ne_zero
    have hprod :
        (qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
            qI.inertiaDegIn (NumberField.RingOfIntegers E)) * b = b := by
      calc
        (qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
            qI.inertiaDegIn (NumberField.RingOfIntegers E)) * b
          =
            (qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
              Q.ramificationIdxIn (NumberField.RingOfIntegers L)) *
              (qI.inertiaDegIn (NumberField.RingOfIntegers E) *
                Q.inertiaDegIn (NumberField.RingOfIntegers L)) := by
                  dsimp [b]
                  ring
        _ =
            qI.ramificationIdxIn (NumberField.RingOfIntegers L) *
              qI.inertiaDegIn (NumberField.RingOfIntegers L) := by
                rw [hramMul, hinMul]
        _ = Nat.card H := by rw [hHfull]
        _ = b := by simpa [b] using hHrel
    have hprod' :
        (qI.ramificationIdxIn (NumberField.RingOfIntegers E) *
            qI.inertiaDegIn (NumberField.RingOfIntegers E)) * b = 1 * b := by
      simpa using hprod.trans (one_mul b).symm
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb_ne_zero) hprod'
  have hramIn : qI.ramificationIdxIn (NumberField.RingOfIntegers E) = 1 := by
    exact Nat.eq_one_of_mul_eq_one_right hmul
  have hinIn : qI.inertiaDegIn (NumberField.RingOfIntegers E) = 1 := by
    exact Nat.eq_one_of_mul_eq_one_left hmul
  have hQe : Ideal.ramificationIdx qI Q = 1 := by
    calc
      Ideal.ramificationIdx qI Q
        = qI.ramificationIdxIn (NumberField.RingOfIntegers E) := by
            symm
            exact Ideal.ramificationIdxIn_eq_ramificationIdx
              (p := qI) (P := Q) (G := Gal(↥E/ℚ))
      _ = 1 := hramIn
  have hQf : Ideal.inertiaDeg qI Q = 1 := by
    calc
      Ideal.inertiaDeg qI Q
        = qI.inertiaDegIn (NumberField.RingOfIntegers E) := by
            symm
            exact Ideal.inertiaDegIn_eq_inertiaDeg
              (p := qI) (P := Q) (G := Gal(↥E/ℚ))
      _ = 1 := hinIn
  exact splits_completely_conditions ↥E hq Q hQe hQf

end Towers
