import Submission.ClassField.CyclotomicBrauer.Cyclotomic
import Submission.ClassField.CyclotomicBrauer.RationalPrimesBelow

/-!
# Lemma VII.7.3: the odd-prime global field

For an odd prime `ell`, the Galois group of
`ℚ(ζ_(ell ^ (a + 1)))` is cyclic of order `ell ^ a * (ell - 1)`.
Taking the fixed field of the subgroup of order `ell - 1` therefore gives
a cyclic cyclotomic extension of `ℚ` of degree `ell ^ a`.

This is the global field used for the odd-prime component of Lemma VII.7.3.
The separate local-degree-growth theorem still has to choose the conductor
large enough relative to the prescribed rational primes.
-/

namespace Submission.CField.CBrauer

open IntermediateField

noncomputable section

universe u

/-- The full odd-primary fixed-field witness, retaining the ambient
cyclotomic field needed for the completion tower. -/
def OddOverfieldWitness (ell a : ℕ) : Prop :=
  ∃ C : Type, ∃ fieldC : Field C,
  letI : Field C := fieldC
  ∃ numberFieldC : NumberField C,
  letI : NumberField C := numberFieldC
  ∃ cyclotomicC : IsCyclotomicExtension {ell ^ (a + 1)} ℚ C,
  letI : IsCyclotomicExtension {ell ^ (a + 1)} ℚ C := cyclotomicC
  ∃ E : IntermediateField ℚ C,
  ∃ numberFieldE : NumberField E,
  letI : NumberField E := numberFieldE
  ∃ galoisE : IsGalois ℚ E,
  letI : IsGalois ℚ E := galoisE
  ∃ _cyclicE : IsCyclic Gal(E/ℚ),
  ∃ _galoisEC : IsGalois E C,
    Module.finrank ℚ E = ell ^ a ∧
      Module.finrank E C = ell - 1

/-- Passing from the full odd-prime cyclotomic field to the fixed field of
its prime-to-`ell` subgroup preserves the required `ell`-power divisibility
of a local degree.

The four natural numbers model the completion tower
`C_w / E_u / ℚ_p`: `fullDegree = relativeDegree * fixedDegree`, while the
relative degree divides the order `ell - 1` of the fixed subgroup. -/
theorem odd_dvd_degree
    (ell a fullDegree relativeDegree fixedDegree : ℕ)
    (hell : ell.Prime)
    (htower : fullDegree = relativeDegree * fixedDegree)
    (hrelative : relativeDegree ∣ ell - 1)
    (hfull : ell ^ a ∣ fullDegree) :
    ell ^ a ∣ fixedDegree := by
  have hellCoprime : ell.Coprime (ell - 1) := by
    rw [hell.coprime_iff_not_dvd]
    intro hdvd
    have hpredPositive : 0 < ell - 1 := Nat.sub_pos_of_lt hell.one_lt
    have hle : ell ≤ ell - 1 := Nat.le_of_dvd hpredPositive hdvd
    omega
  have hpowCoprime : (ell ^ a).Coprime (ell - 1) :=
    hellCoprime.pow_left a
  have hrelativeCoprime : (ell ^ a).Coprime relativeDegree :=
    Nat.Coprime.coprime_dvd_right hrelative hpowCoprime
  apply hrelativeCoprime.dvd_of_dvd_mul_left
  rwa [← htower]

/-- For every odd prime `ell`, there is a cyclic cyclotomic extension of
`ℚ` having degree exactly `ell ^ a`.  Concretely it is the fixed field of
the subgroup of order `ell - 1` in the full cyclotomic field of conductor
`ell ^ (a + 1)`.

This theorem isolates the global Galois-theoretic part of the
prime-power block construction from its remaining local-degree argument. -/
theorem odd_overfield_witness
    (ell a : ℕ) (hell : ell.Prime) (hell2 : ell ≠ 2) :
    OddOverfieldWitness ell a := by
  letI : NeZero (ell ^ (a + 1)) :=
    ⟨pow_ne_zero (a + 1) hell.ne_zero⟩
  let C := CyclotomicField (ell ^ (a + 1)) ℚ
  letI : Field C := inferInstance
  letI : NumberField C := inferInstance
  letI : Algebra ℚ C := inferInstance
  letI : IsCyclotomicExtension {ell ^ (a + 1)} ℚ C :=
    CyclotomicField.isCyclotomicExtension (ell ^ (a + 1)) ℚ
  letI : FiniteDimensional ℚ C := inferInstance
  letI : IsGalois ℚ C :=
    cyclotomic_isGalois (n := ell ^ (a + 1))
  letI : Finite Gal(C/ℚ) := inferInstance
  letI : IsCyclic Gal(C/ℚ) :=
    odd_aut_cyclic
      (p := ell) (r := a + 1) hell hell2 ℚ C
  letI : CommGroup Gal(C/ℚ) := IsCyclic.commGroup
  have hcard : Nat.card Gal(C/ℚ) = ell ^ a * (ell - 1) := by
    rw [IsGalois.card_aut_eq_finrank]
    simpa only [Nat.add_sub_cancel] using
      (rational_cyclotomic_finrank
        (p := ell) (r := a + 1) hell (Nat.succ_pos a) C)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(C/ℚ))
  have hgorder : orderOf g = ell ^ a * (ell - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  let H : Subgroup Gal(C/ℚ) := Subgroup.zpowers (g ^ ell ^ a)
  have hpow_ne : ell ^ a ≠ 0 := pow_ne_zero a hell.ne_zero
  have hpowa_dvd_order : ell ^ a ∣ orderOf g := by
    rw [hgorder]
    exact dvd_mul_right _ _
  have hHcard : Nat.card H = ell - 1 := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hpow_ne hpowa_dvd_order,
      hgorder, Nat.mul_div_right _ (Nat.pos_of_ne_zero hpow_ne)]
  have hHindex : H.index = ell ^ a := by
    have hmul := H.card_mul_index
    rw [hHcard, hcard] at hmul
    have hellpred : 0 < ell - 1 := Nat.sub_pos_of_lt hell.one_lt
    have hmul' : (ell - 1) * H.index = (ell - 1) * ell ^ a := by
      simpa only [Nat.mul_comm] using hmul
    exact Nat.eq_of_mul_eq_mul_left hellpred hmul'
  let E : IntermediateField ℚ C := IntermediateField.fixedField H
  letI : H.Normal := by infer_instance
  letI : IsGalois ℚ E := by
    dsimp only [E]
    exact IsGalois.of_fixedField_normal_subgroup H
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : IsCyclic Gal(E/ℚ) := by
    letI : IsCyclic (Gal(C/ℚ) ⧸ H) :=
      isCyclic_of_surjective (QuotientGroup.mk' H)
        (QuotientGroup.mk'_surjective H)
    exact (IsGalois.normalAutEquivQuotient H).isCyclic.mp inferInstance
  have hEdegree : Module.finrank ℚ E = ell ^ a := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := E),
      IntermediateField.fixingSubgroup_fixedField, hHindex]
  have hrelative : Module.finrank E C = ell - 1 := by
    change Module.finrank (IntermediateField.fixedField H) C = ell - 1
    rw [IntermediateField.finrank_fixedField_eq_card H, hHcard]
  refine ⟨C, inferInstance, inferInstance, inferInstance, E, inferInstance,
    inferInstance, inferInstance, inferInstance, hEdegree, hrelative⟩

/-- The overfield witness packages to the original finite-extension output
while retaining a separate stronger theorem for local completion work. -/
theorem odd_extension_data
    (ell a : ℕ) (hell : ell.Prime) (hell2 : ell ≠ 2) :
    ∃ data : FEData ℚ,
      data.IsCyclicCyclotomic ∧
        letI : Field data.L := data.fieldL
        letI : Algebra ℚ data.L := data.algebraKL
        Module.finrank ℚ data.L = ell ^ a := by
  rcases odd_overfield_witness ell a hell hell2 with
    ⟨C, fieldC, numberFieldC, cyclotomicC, E, numberFieldE,
      galoisE, cyclicE, galoisEC, hEdegree, _hrelative⟩
  letI : Field C := fieldC
  letI : NumberField C := numberFieldC
  letI : IsCyclotomicExtension {ell ^ (a + 1)} ℚ C := cyclotomicC
  letI : NumberField E := numberFieldE
  letI : IsGalois ℚ E := galoisE
  letI : IsCyclic Gal(E/ℚ) := cyclicE
  letI : IsGalois E C := galoisEC
  let data : FEData ℚ :=
    { L := E
      fieldL := inferInstance
      numberFieldL := inferInstance
      algebraKL := E.algebra'
      finiteDimensionalKL := inferInstance
      isGaloisKL := galoisE }
  refine ⟨data, ?_, ?_⟩
  · change IsCyclic Gal(E/ℚ) ∧ _
    refine ⟨inferInstance, ell ^ (a + 1), C, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, trivial⟩
  · exact hEdegree

end

end Submission.CField.CBrauer
