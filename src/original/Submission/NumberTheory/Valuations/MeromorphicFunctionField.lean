import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.RingTheory.Valuation.Basic


/-!
# The meromorphic-function valuation at a point

For a nonempty connected open subset `U` of `ℂ`, meromorphic functions are considered modulo
equality away from a discrete subset of `U`.  The resulting ring is a field: a nonzero
meromorphic function is nonzero away from a discrete subset, so pointwise inversion becomes a
genuine inverse after passing to codiscrete germs.

At every `P ∈ U`, `meromorphicOrderAt` descends to this field and defines a surjective additive
valuation with value group `ℤ`.  This is the complex-open-set form of Milne, Example 3.26(a).
-/

namespace Submission.NumberTheory.Milne

open Filter Topology

/-- The hypotheses under which meromorphic functions on `U` form a field.  `IsConnected`
includes nonemptiness. -/
class MFDomain (U : Set ℂ) : Prop where
  isOpen : IsOpen U
  isConnected : IsConnected U

namespace MFDomain

variable {U : Set ℂ} [MFDomain U]

theorem nonempty : U.Nonempty :=
  (MFDomain.isConnected (U := U)).nonempty

/-- Every point of a meromorphic-function domain is an accumulation point of the domain. -/
theorem accPt (P : U) : AccPt (P : ℂ) (Filter.principal U) := by
  rw [accPt_principal_iff_nhdsWithin]
  have hU : U ∈ nhdsWithin (P : ℂ) ({(P : ℂ)}ᶜ) :=
    mem_nhdsWithin_of_mem_nhds
      (MFDomain.isOpen.mem_nhds P.property)
  rw [Set.diff_eq, nhdsWithin_inter_of_mem hU]
  exact PerfectSpace.not_isolated (P : ℂ)

/-- The codiscrete filter on a nonempty open subset of `ℂ` is nontrivial. -/
instance codiscrete_within_bot : NeBot (codiscreteWithin U) := by
  let P : U := ⟨(nonempty (U := U)).choose, (nonempty (U := U)).choose_spec⟩
  have hP : NeBot (nhdsWithin (P : ℂ) (U \ {(P : ℂ)})) :=
    accPt_principal_iff_nhdsWithin.mp (accPt P)
  apply hP.mono
  exact le_iSup_of_le (P : ℂ) (le_iSup_of_le P.property le_rfl)

end MFDomain

/-- The subring of codiscrete germs on `U` admitting a meromorphic representative. -/
def meromorphicFunctionSubring (U : Set ℂ) :
    Subring (Germ (codiscreteWithin U) ℂ) where
  carrier F := ∃ f : ℂ → ℂ, MeromorphicOn f U ∧ (f : Germ (codiscreteWithin U) ℂ) = F
  zero_mem' := ⟨0, MeromorphicOn.const 0, rfl⟩
  one_mem' := ⟨1, MeromorphicOn.const 1, rfl⟩
  add_mem' := by
    rintro F G ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro F G ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro F ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

/-- The field of meromorphic functions on `U`, represented by codiscrete germs. -/
def MFField (U : Set ℂ) :=
  meromorphicFunctionSubring U

namespace MFField

variable {U : Set ℂ} [MFDomain U]

/-- A meromorphic function gives an element of the meromorphic-function field. -/
noncomputable def ofFunction (f : ℂ → ℂ) (hf : MeromorphicOn f U) :
    MFField U :=
  ⟨(f : Germ (codiscreteWithin U) ℂ), f, hf, rfl⟩

omit [MFDomain U] in
@[simp]
theorem ofFunction_val (f : ℂ → ℂ) (hf : MeromorphicOn f U) :
    (ofFunction f hf : Germ (codiscreteWithin U) ℂ) = f :=
  rfl

/-- A nonzero meromorphic codiscrete germ has a representative which is nonzero on a
codiscrete subset. -/
theorem eventually_ne_germ
    {f : ℂ → ℂ} (hf : MeromorphicOn f U)
    (hf0 : (f : Germ (codiscreteWithin U) ℂ) ≠ 0) :
    ∀ᶠ z in codiscreteWithin U, f z ≠ 0 := by
  have hexists : ∃ P : U, meromorphicOrderAt f P ≠ ⊤ := by
    by_contra h
    push Not at h
    apply hf0
    apply Germ.coe_eq.mpr
    rw [EventuallyEq, Filter.Eventually,
      mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro P hPU
    have hzero : f =ᶠ[nhdsWithin P ({P}ᶜ)] 0 :=
      meromorphicOrderAt_eq_top_iff.mp (h ⟨P, hPU⟩)
    filter_upwards [hzero] with z hz
    simp [hz]
  have hfinite : ∀ P : U, meromorphicOrderAt f P ≠ ⊤ :=
    (hf.exists_meromorphicOrderAt_ne_top_iff_forall
      MFDomain.isConnected).mp hexists
  rw [Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro P hPU
  have hne : ∀ᶠ z in nhdsWithin P ({P}ᶜ), f z ≠ 0 :=
    (hf P hPU).eventually_eq_zero_or_eventually_ne_zero.resolve_left <| by
      intro hzero
      exact (hfinite ⟨P, hPU⟩) (meromorphicOrderAt_eq_top_iff.mpr hzero)
  filter_upwards [hne] with z hz
  simp [hz]

/-- Inversion of codiscrete germs preserves meromorphy. -/
noncomputable instance : Inv (MFField U) where
  inv F := ⟨F.1⁻¹, by
    rcases F.2 with ⟨f, hf, hF⟩
    exact ⟨f⁻¹, hf.inv, by rw [Germ.coe_inv, hF]⟩⟩

omit [MFDomain U] in
@[simp]
theorem val_inv (F : MFField U) :
    ((F⁻¹ : MFField U) : Germ (codiscreteWithin U) ℂ) = F.1⁻¹ :=
  rfl

theorem mul_inv_cancel (F : MFField U) (hF : F ≠ 0) : F * F⁻¹ = 1 := by
  apply Subtype.ext
  rcases F.2 with ⟨f, hf, hrep⟩
  have hrep0 : (f : Germ (codiscreteWithin U) ℂ) ≠ 0 := by
    intro hf0
    apply hF
    apply Subtype.ext
    exact hrep.symm.trans hf0
  change F.1 * F.1⁻¹ = 1
  rw [← hrep, ← Germ.coe_inv, ← Germ.coe_mul]
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_ne_germ hf hrep0] with z hz
  exact mul_inv_cancel₀ hz

omit [MFDomain U] in
@[simp]
theorem inv_zero : (0 : MFField U)⁻¹ = 0 := by
  apply Subtype.ext
  change (0 : Germ (codiscreteWithin U) ℂ)⁻¹ = 0
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun _ ↦ by simp [Function.comp_apply]

/-- Meromorphic codiscrete germs form a field. -/
noncomputable instance : Field (MFField U) :=
  Field.ofMinimalAxioms _ add_assoc zero_add neg_add_cancel mul_assoc mul_comm one_mul
    mul_inv_cancel inv_zero left_distrib
    ⟨0, 1, by
      intro h
      have hval := congrArg Subtype.val h
      exact zero_ne_one hval⟩

/-- A chosen meromorphic representative of a meromorphic-function-field element. -/
noncomputable def representative (F : MFField U) : ℂ → ℂ :=
  F.2.choose

omit [MFDomain U] in
theorem represent_meromorp (F : MFField U) :
    MeromorphicOn (representative F) U :=
  F.2.choose_spec.1

omit [MFDomain U] in
theorem representative_germ (F : MFField U) :
    (representative F : Germ (codiscreteWithin U) ℂ) = F.1 :=
  F.2.choose_spec.2

/-- Codiscrete equality of meromorphic functions implies punctured-neighborhood equality at
every point of an open domain. -/
theorem eventually_nhds_germ
    {f g : ℂ → ℂ} (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (hfg : (f : Germ (codiscreteWithin U) ℂ) = g) (P : U) :
    f =ᶠ[nhdsWithin (P : ℂ) ({(P : ℂ)}ᶜ)] g := by
  apply (hf P P.property).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
    (hg P P.property) P.property (MFDomain.accPt P)
  exact Germ.coe_eq.mp hfg

/-- The additive order of a meromorphic-function-field element at `P`. -/
noncomputable def orderAt (P : U) (F : MFField U) : WithTop ℤ :=
  meromorphicOrderAt (representative F) P

/-- The order can be computed using any meromorphic representative. -/
theorem order_function
    (P : U) {f : ℂ → ℂ} (hf : MeromorphicOn f U)
    (F : MFField U)
    (hF : (f : Germ (codiscreteWithin U) ℂ) = F.1) :
    orderAt P F = meromorphicOrderAt f P := by
  apply meromorphicOrderAt_congr
  exact eventually_nhds_germ (represent_meromorp F) hf
    ((representative_germ F).trans hF.symm) P

@[simp]
theorem orderAt_zero (P : U) : orderAt P (0 : MFField U) = ⊤ := by
  rw [order_function P (MeromorphicOn.const 0) 0 rfl,
    meromorphicOrderAt_const]
  simp

@[simp]
theorem orderAt_one (P : U) : orderAt P (1 : MFField U) = 0 := by
  rw [order_function P (MeromorphicOn.const 1) 1 rfl,
    meromorphicOrderAt_const]
  simp

theorem orderAt_mul (P : U) (F G : MFField U) :
    orderAt P (F * G) = orderAt P F + orderAt P G := by
  rw [order_function P
    ((represent_meromorp F).mul (represent_meromorp G)) (F * G)]
  · exact meromorphicOrderAt_mul
      (represent_meromorp F P P.property)
      (represent_meromorp G P P.property)
  · rw [Germ.coe_mul, representative_germ F, representative_germ G]
    rfl

theorem orderAt_add (P : U) (F G : MFField U) :
    min (orderAt P F) (orderAt P G) ≤ orderAt P (F + G) := by
  rw [order_function P
    ((represent_meromorp F).add (represent_meromorp G)) (F + G)]
  · exact meromorphicOrderAt_add
      (represent_meromorp F P P.property)
      (represent_meromorp G P P.property)
  · rw [Germ.coe_add, representative_germ F, representative_germ G]
    rfl

/-- Example 3.26(a): order at `P` is an additive discrete valuation on the field of meromorphic
functions on `U`. -/
noncomputable def orderValuation (P : U) :
    AddValuation (MFField U) (WithTop ℤ) :=
  AddValuation.of (orderAt P) (orderAt_zero P) (orderAt_one P)
    (orderAt_add P) (orderAt_mul P)

@[simp]
theorem orderValuation_apply (P : U) (F : MFField U) :
    orderValuation P F = orderAt P F :=
  rfl

/-- The order valuation is normalized: every integer value, as well as the value `⊤` at zero,
occurs. -/
theorem orderValuation_surjective (P : U) :
    Function.Surjective (orderValuation P) := by
  intro n
  cases n with
  | top =>
      exact ⟨0, orderAt_zero P⟩
  | coe n =>
      let f : ℂ → ℂ := (· - (P : ℂ)) ^ n
      have hf : MeromorphicOn f U := by
        apply MeromorphicOn.zpow
        exact MeromorphicOn.id.sub (MeromorphicOn.const (P : ℂ))
      let F := ofFunction f hf
      refine ⟨F, ?_⟩
      rw [orderValuation_apply, order_function P hf F rfl]
      exact meromorphicOrderAt_zpow_id_sub_const

end MFField

end Submission.NumberTheory.Milne
