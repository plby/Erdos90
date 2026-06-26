import Mathlib.GroupTheory.PGroup
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Ring.Compact
import Submission.ClassField.UnramifiedCohom.PrincipalUnits
import Submission.ClassField.LocalBrauer.UnramifiedNormSurjectivity

/-!
# Class Field Theory, Chapter I, paragraph 1.9: principal-unit quotients

Milne notes that the successive quotients
`(1 + mathfrak m^m) / (1 + mathfrak m^(m+1))`, for `m > 0`, are `p`-groups,
where `p` is the residue characteristic.  The later principal-unit
calculation from Lemma III.1.3 identifies this quotient with the additive
group of the residue field, from which the claim follows.
-/

namespace Submission.CField.NCorr

open Filter
open IsLocalRing ValuativeRel
open scoped Topology

noncomputable section

/-- The `m`th principal-unit subgroup of a commutative local ring. -/
abbrev principalUnitSubgroup (R : Type*) [CommRing R] [IsLocalRing R]
    (m : Nat) : Subgroup Rˣ :=
  Edmonton.idealUnitSubgroup (maximalIdeal R) m

section LocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsDomain R]
variable {p : Nat} [CharP (ResidueField R) p]

/-- For a local domain with nonzero principal maximal ideal, each positive
successive principal-unit quotient is a group of residue-characteristic
power order in the elementwise sense of `IsPGroup`. -/
theorem principal_unit_group
    (hprincipal : (maximalIdeal R).IsPrincipal)
    (hne : maximalIdeal R ≠ ⊥) (m : Nat) (hm : 0 < m) :
    IsPGroup p
      (principalUnitSubgroup R m ⧸
        (principalUnitSubgroup R (m + 1)).subgroupOf
          (principalUnitSubgroup R m)) := by
  letI : Module (ZMod p) (ResidueField R) :=
    { (ZMod.castHom dvd_rfl (ResidueField R)).toModule with }
  exact
    (ZModModule.isPGroup_multiplicative
      (n := p) (G := ResidueField R)).of_equiv
        (Submission.CField.UCohom.principalSuccessiveResidue
            R hprincipal hne m hm).symm

end LocalRing

section LocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {p : Nat} [CharP 𝓀[K] p]

/-- Paragraph 1.9 for a nonarchimedean local field: every positive
successive principal-unit quotient is a `p`-group. -/
theorem principal_p_group (m : Nat) (hm : 0 < m) :
    IsPGroup p
      (principalUnitSubgroup 𝒪[K] m ⧸
        (principalUnitSubgroup 𝒪[K] (m + 1)).subgroupOf
          (principalUnitSubgroup 𝒪[K] m)) := by
  apply principal_unit_group 𝒪[K]
  · exact IsPrincipalIdealRing.principal _
  · simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  · exact hm

end LocalField

section NeighborhoodBasis

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsNonarchimedeanLocalField K]

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- Every principal-unit subgroup is a neighborhood of one in the local
unit group. -/
theorem principal_unit_nhds (m : ℕ) :
    (principalUnitSubgroup 𝒪[K] m : Set 𝒪[K]ˣ) ∈
      𝓝 (1 : 𝒪[K]ˣ) := by
  let I := maximalIdeal 𝒪[K]
  have hopen : IsOpen ((I ^ m : Ideal 𝒪[K]) : Set 𝒪[K]) := by
    exact IsLocalRing.isOpen_maximalIdeal_pow 𝒪[K] m
  have hcontinuous : Continuous (fun u : 𝒪[K]ˣ => (u : 𝒪[K]) - 1) :=
    Units.continuous_val.sub continuous_const
  change {u : 𝒪[K]ˣ | (u : 𝒪[K]) - 1 ∈ I ^ m} ∈ 𝓝 1
  exact (hopen.preimage hcontinuous).mem_nhds (by simp)

/-- Paragraph 1.9: the principal-unit filtration is a neighborhood basis of
one in the unit group of a nonarchimedean local field. -/
theorem principal_unit_basis :
    (𝓝 (1 : 𝒪[K]ˣ)).HasBasis (fun _ : ℕ => True)
      (fun m => (principalUnitSubgroup 𝒪[K] m : Set 𝒪[K]ˣ)) := by
  rw [Filter.hasBasis_iff]
  intro V
  constructor
  · intro hV
    obtain ⟨m, hm⟩ :=
      LBrauer.principal_eventually_subset K V hV
    exact ⟨m, trivial, hm⟩
  · rintro ⟨m, -, hm⟩
    exact Filter.mem_of_superset (principal_unit_nhds K m) hm

end NeighborhoodBasis

end

end Submission.CField.NCorr
