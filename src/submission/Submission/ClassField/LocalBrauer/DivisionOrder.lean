import Submission.ClassField.CrossedProducts.IsMulCoboundary
import Submission.ClassField.LocalBrauer.CanonicalUnramifiedRelative
import Submission.ClassField.LocalBrauer.CofinalityUnconditional

/-!
# The order of the Brauer class of a local division algebra

The unramified maximal subfield of a central division algebra has degree equal
to the degree of the algebra and splits it.  After identifying that subfield
with the canonical unramified extension, it is Galois.  The standard exponent
bound for a relative Brauer group therefore shows that the order of the
division algebra's Brauer class divides its degree.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups CProduca

variable (K D : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
  [Module.Finite K D]

set_option maxHeartbeats 1600000 in
-- Constructing and identifying the maximal unramified subfield is expensive.
/-- The period of a finite-dimensional central division algebra over a local
field divides its degree. -/
theorem division_sqrt_finrank :
    orderOf (brauerClass K (centralDivisionCSA K D)) ∣
      Nat.sqrt (Module.finrank K D) := by
  let ambientUniformSpace : UniformSpace K := inferInstance
  let ambientIsUniformAddGroup : IsUniformAddGroup K := inferInstance
  let ambientNormedField : NontriviallyNormedField K := inferInstance
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : Valuation.RankOne
      (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)) := by
    change Valuation.RankOne (valuation K)
    infer_instance
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  letI : Valuation.Compatible (NormedField.valuation (K := K)) := by
    constructor
    intro a b
    change a ≤ᵥ b ↔ ‖a‖₊ ≤ ‖b‖₊
    rw [← NNReal.coe_le_coe]
    change a ≤ᵥ b ↔ ‖a‖ ≤ ‖b‖
    rw [Valued.toNormedField.norm_le_iff]
    exact (ValuativeRel.valuation K).vle_iff_le
  obtain ⟨alpha, hcomm, hdegree, _hmaximal, hsplitD, hunramified⟩ :=
    splitting_subfield_unconditional K D
  letI : UniformSpace K := ambientUniformSpace
  letI : IsUniformAddGroup K := ambientIsUniformAddGroup
  letI : NontriviallyNormedField K := ambientNormedField
  let E := Algebra.adjoin K ({(alpha : D)} : Set D)
  letI : CommRing E := { (inferInstance : Ring E) with mul_comm := hcomm }
  letI : Module.Finite K E :=
    Module.Finite.of_injective E.val.toLinearMap Subtype.val_injective
  letI : IsDomain E :=
    Function.Injective.isDomain E.val.toRingHom Subtype.val_injective
  letI : Field E := fieldOfFiniteDimensional K E
  let e : E :=
    ⟨(alpha : D), Algebra.subset_adjoin
      (Set.mem_singleton (alpha : D))⟩
  have hmodel : UnramifiedIntegralGenerator K E := by
    obtain ⟨he, hformal, hlocal, _hdvr, _hunramifiedAt⟩ := hunramified
    refine ⟨e, ?_, he, hformal, hlocal⟩
    apply Subalgebra.map_injective (f := E.val) Subtype.val_injective
    rw [AlgHom.map_adjoin_singleton, Algebra.map_top]
    simpa [E, e] using (Subalgebra.range_val E).symm
  obtain ⟨eCanonical⟩ :=
    unramified_uniqueness_unconditional K E hmodel
  letI : IsGalois K E := IsGalois.of_algEquiv eCanonical.symm
  have hmem :
      brauerClass K (centralDivisionCSA K D) ∈ relativeBrauerGroup K E :=
    (brauer_relative_split
      K E (centralDivisionCSA K D)).2 hsplitD
  let y : relativeBrauerGroup K E :=
    ⟨brauerClass K (centralDivisionCSA K D), hmem⟩
  have hy := relative_brauer_one K E y
  have hpow :
      (brauerClass K (centralDivisionCSA K D)) ^ Module.finrank K E = 1 :=
    congrArg Subtype.val hy
  have hord := orderOf_dvd_of_pow_eq_one hpow
  change Module.finrank K E = Nat.sqrt (Module.finrank K D) at hdegree
  rw [hdegree] at hord
  exact hord

/-- A central simple algebra over a local field is a division algebra if the
order of its Brauer class equals its degree. -/
theorem domain_sqrt_finrank
    (A : Type u) [Ring A] [Algebra K A] [IsSimpleRing A]
    [Algebra.IsCentral K A] [Module.Finite K A]
    (hperiod :
      orderOf (brauerClass K (centralSimpleCSA K A)) =
        Nat.sqrt (Module.finrank K A)) :
    IsDomain A := by
  obtain ⟨q, hq, D, hDdiv, hDalg, hDcentral, hDfinite, ⟨eA⟩⟩ :=
    matrix_division_algebra K A
  letI : NeZero q := hq
  letI : DivisionRing D := hDdiv
  letI : Algebra K D := hDalg
  letI : Algebra.IsCentral K D := hDcentral
  letI : Module.Finite K D := hDfinite
  have hAD : IsBrauerEquivalent
      (centralSimpleCSA K A) (centralDivisionCSA K D) := by
    refine ⟨1, q, one_ne_zero, NeZero.ne q, ?_⟩
    exact ⟨(matrixFinAlg K A).trans eA⟩
  have hclass :
      brauerClass K (centralSimpleCSA K A) =
        brauerClass K (centralDivisionCSA K D) :=
    (brauer_class K _ _).2 hAD
  obtain ⟨a, ha⟩ := finrank_simple_square K A
  obtain ⟨d, hd⟩ := finrank_simple_square K D
  have hdPos : 0 < d := by
    have : 0 < d ^ 2 := by simpa [hd] using (Module.finrank_pos :
      0 < Module.finrank K D)
    exact Nat.pos_of_ne_zero fun hdZero ↦ by simp [hdZero] at this
  have haSqrt : Nat.sqrt (Module.finrank K A) = a := by simp [ha]
  have hdSqrt : Nat.sqrt (Module.finrank K D) = d := by simp [hd]
  have hadSq : a ^ 2 = (q * d) ^ 2 := by
    calc
      a ^ 2 = Module.finrank K A := ha.symm
      _ = Module.finrank K (Matrix (Fin q) (Fin q) D) :=
        eA.toLinearEquiv.finrank_eq
      _ = q * q * Module.finrank K D := by
        rw [Module.finrank_matrix, Fintype.card_fin]
      _ = (q * d) ^ 2 := by rw [hd]; ring
  have had : a = q * d :=
    Nat.pow_left_injective (by decide : 2 ≠ 0) hadSq
  have hdiv : a ∣ d := by
    have h := division_sqrt_finrank K D
    rw [← hclass, hperiod, haSqrt, hdSqrt] at h
    exact h
  have hadLe : a ≤ d := Nat.le_of_dvd hdPos hdiv
  have hqdLe : q * d ≤ 1 * d := by simpa [had] using hadLe
  have hqLe : q ≤ 1 :=
    (Nat.mul_le_mul_right_iff hdPos).mp hqdLe
  have hqOne : q = 1 :=
    Nat.le_antisymm hqLe (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  subst q
  let eAD : A ≃ₐ[K] D :=
    eA.trans (matrixFinAlg K D)
  exact eAD.toRingEquiv.toMulEquiv.isDomain

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The degree of a central division algebra divides the degree of every
finite splitting field. -/
theorem sqrt_dvd_split
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    (hsplit : ISBy K L D) :
    Nat.sqrt (Module.finrank K D) ∣ Module.finrank K L := by
  obtain ⟨B, i, hi, hBdim, hDB⟩ :=
    (split_similar_containing K L D).1 hsplit
  obtain ⟨q, hq, E, hEdiv, hEalg, hEcentral, hEfinite, ⟨eB⟩⟩ :=
    matrix_division_algebra K B
  letI : NeZero q := hq
  letI : DivisionRing E := hEdiv
  letI : Algebra K E := hEalg
  letI : Algebra.IsCentral K E := hEcentral
  letI : Module.Finite K E := hEfinite
  have hBE : IsBrauerEquivalent B (centralDivisionCSA K E) := by
    refine ⟨1, q, one_ne_zero, NeZero.ne q, ?_⟩
    exact ⟨(matrixFinAlg K B).trans eB⟩
  have hDE : IsBrauerEquivalent
      (centralDivisionCSA K D) (centralDivisionCSA K E) :=
    hDB.trans hBE
  obtain ⟨eDE⟩ :=
    (division_brauer_equivalent K D E).1 hDE
  obtain ⟨d, hd⟩ := finrank_simple_square K D
  have hsquare : (Module.finrank K L) ^ 2 = (q * d) ^ 2 := by
    calc
      (Module.finrank K L) ^ 2 = Module.finrank K B := hBdim.symm
      _ = Module.finrank K (Matrix (Fin q) (Fin q) E) :=
        eB.toLinearEquiv.finrank_eq
      _ = q * q * Module.finrank K E := by
        rw [Module.finrank_matrix, Fintype.card_fin]
      _ = q * q * Module.finrank K D := by
        rw [eDE.toLinearEquiv.finrank_eq]
      _ = (q * d) ^ 2 := by rw [hd]; ring
  have hdegree : Module.finrank K L = q * d :=
    Nat.pow_left_injective (by decide : 2 ≠ 0) hsquare
  rw [hd]
  simp only [Nat.sqrt_eq']
  exact ⟨q, by simpa [mul_comm] using hdegree⟩

/-- If a division algebra is split by an extension whose degree is its
period, then its period equals its degree. -/
theorem division_sqrt_split
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    (hdegree : Module.finrank K L =
      orderOf (brauerClass K (centralDivisionCSA K D)))
    (hsplit : ISBy K L D) :
    orderOf (brauerClass K (centralDivisionCSA K D)) =
      Nat.sqrt (Module.finrank K D) := by
  apply Nat.dvd_antisymm
  · exact division_sqrt_finrank K D
  · rw [← hdegree]
    exact sqrt_dvd_split K D L hsplit

/-- Remark IV.4.4(b): over a nonarchimedean local field, the period of a
central division algebra equals its degree. -/
theorem brauer_division_finrank :
    orderOf (brauerClass K (centralDivisionCSA K D)) =
      Nat.sqrt (Module.finrank K D) := by
  let x := brauerClass K (centralDivisionCSA K D)
  have hxFinite : IsOfFinOrder x := brauer_group_torsion K x
  have hxPos : 0 < orderOf x := hxFinite.orderOf_pos
  let E := canonicalUnramifiedLevel K (orderOf x)
  letI : NeZero (orderOf x) := ⟨hxPos.ne'⟩
  have hxmem : x ∈ relativeBrauerGroup K E :=
    relative_level_order K x hxPos
  have hsplit : ISBy K E D :=
    (brauer_relative_split
      K E (centralDivisionCSA K D)).1 hxmem
  apply
    division_sqrt_split
      K D E
  · exact unramified_level_finrank K (orderOf x)
  · exact hsplit

end

end Submission.CField.LBrauer
