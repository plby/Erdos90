import Submission.ClassField.BrauerGroups.CentralDivisionCSA
import Submission.ClassField.CrossedProducts.RelativeGroupMono
import Submission.ClassField.LocalBrauer.CanonicalUnramifiedTower
import Submission.ClassField.LocalBrauer.DivisionAlgebraStructure

/-!
# Cofinality of the canonical unramified tower

The structure theorem for local division algebras already supplies an
unramified maximal splitting field for every division representative.  This
file isolates the remaining uniqueness input and proves the rest of the
cofinality argument: once every finite field with the resulting unramified
integral model is identified with the canonical level of the same degree,
the factorial canonical tower splits every Brauer class.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups CProduca

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The integral unramifiedness property needed for uniqueness: the field has
a primitive integral generator whose integer algebra is local and formally
unramified.  Finiteness and formal unramifiedness force this local domain to
be a DVR and imply unramifiedness at its maximal ideal. -/
def UnramifiedIntegralGenerator
    (E : Type u) [Field E] [Algebra K E] : Prop :=
  let OR := (ValuativeRel.valuation K).integer
  let g : OR →+* E := (algebraMap K E).comp OR.subtype
  letI : Algebra OR E := g.toAlgebra
  ∃ e : E,
    let U := Algebra.adjoin OR ({e} : Set E)
    Algebra.adjoin K ({e} : Set E) = ⊤ ∧
      IsIntegral OR e ∧
      Algebra.FormallyUnramified OR U ∧
      IsLocalRing U

/-- The uniqueness statement for finite unramified extensions in the exact
form needed by the Brauer cofinality argument. -/
def CanonicalUnramifiedUniqueness : Prop :=
  ∀ (E : Type u) [Field E] [Algebra K E] [Module.Finite K E],
    UnramifiedIntegralGenerator K E →
      Nonempty
        (E ≃ₐ[K] canonicalUnramifiedLevel K (Module.finrank K E))

/-- Every positive integer divides a factorial level of the canonical
unramified tower. -/
private theorem dvd_factorial_level (n : ℕ) (hn : 0 < n) :
    n ∣ invariantLevelDegree n := by
  apply Nat.dvd_factorial hn
  simp

set_option maxHeartbeats 1600000 in
-- Unpacking the maximal splitting subfield requires a larger elaboration budget.
set_option synthInstance.maxHeartbeats 200000 in
-- Unpacking the dependent maximal-subfield theorem and its local instances is expensive.
/-- Subject only to uniqueness of finite unramified extensions, the
factorial canonical tower is cofinal for splitting Brauer classes. -/
theorem factorial_level_cofinal
    (hunique : CanonicalUnramifiedUniqueness K) :
    ∀ x : BrauerGroup K,
      ∃ r, x ∈ relativeBrauerGroup K
        (unramifiedFactorialLevel K r) := by
  intro x
  induction x using Quotient.inductionOn with
  | _ A =>
      obtain ⟨D, hDdiv, hDalg, hDcentral, hDfinite, hAD⟩ :=
        division_brauer_representative K A
      letI : DivisionRing D := hDdiv
      letI : Algebra K D := hDalg
      letI : Algebra.IsCentral K D := hDcentral
      letI : Module.Finite K D := hDfinite
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
      obtain ⟨eCanonical⟩ := hunique E hmodel
      let n := Module.finrank K E
      have hn : 0 < n := Module.finrank_pos
      letI : NeZero n := ⟨hn.ne'⟩
      have hsplitCanonicalD :
          ISBy K (canonicalUnramifiedLevel K n) D := by
        letI : IsSimpleRing E :=
          commutative_subalgebra_simple K D E hcomm
        letI : Algebra E (canonicalUnramifiedLevel K n) :=
          eCanonical.toRingHom.toAlgebra
        letI : IsScalarTower K E (canonicalUnramifiedLevel K n) :=
          IsScalarTower.of_algebraMap_eq fun a ↦ (eCanonical.commutes a).symm
        exact ISBy.tower K E (canonicalUnramifiedLevel K n) D hsplitD
      have hsplitCanonicalA :
          ISBy K (canonicalUnramifiedLevel K n) A :=
        split_equivalent K (canonicalUnramifiedLevel K n)
          A D hAD hsplitCanonicalD
      have hmemLevel :
          (Quotient.mk'' A : BrauerGroup K) ∈
            relativeBrauerGroup K (canonicalUnramifiedLevel K n) :=
        (brauer_relative_split
          K (canonicalUnramifiedLevel K n) A).2 hsplitCanonicalA
      refine ⟨n, relative_brauer_mono K ?_ hmemLevel⟩
      exact unramified_level K hn
        (invariant_level_pos n)
        (dvd_factorial_level n hn)

end

end Submission.CField.LBrauer
