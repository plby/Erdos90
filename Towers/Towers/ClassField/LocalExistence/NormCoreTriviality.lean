import Mathlib.GroupTheory.ResiduallyFinite
import Towers.ClassField.NormCorrespondence.StandardOpenSubgroups
import Towers.ClassField.LocalExistence.ConcreteLocalExistence
import Towers.ClassField.LocalExistence.SeparatingNormFamily

/-!
# Milne, Section III.5, Step 4: triviality of the local norm core

The canonical unramified norm groups force the common norm core into the
local units.  The principal-unit filtration then gives the separating family
used in Step 4.  The final theorem isolates the one input established in
Milne's preceding Steps 2--3: divisibility of the common norm core.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.NCorr
open ValuativeRel

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The principal-unit subgroups of the valuation ring have trivial
intersection.  This is the separatedness content of their neighborhood
basis at one. -/
theorem i_inf_principal :
    (⨅ m : ℕ, principalUnitSubgroup 𝒪[K] m) = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 1
    have hsep := biInter_basis_nhds (principal_unit_basis K)
    have hx' : x ∈ ⋂ (m : ℕ) (_ : True),
        (principalUnitSubgroup 𝒪[K] m : Set 𝒪[K]ˣ) := by
      rw [Set.mem_iInter]
      intro m
      rw [Set.mem_iInter]
      intro _
      exact (Subgroup.mem_iInf.mp hx m)
    rw [hsep] at hx'
    exact hx'
  · exact bot_le

/-- The principal-unit subgroups, mapped into `Kˣ`, still have trivial
intersection. -/
theorem i_inf_bot :
    (⨅ m : ℕ, principalUnitField K m) = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 1
    have hxall : ∀ m : ℕ, x ∈ principalUnitField K m :=
      Subgroup.mem_iInf.mp hx
    obtain ⟨u, hu, hux⟩ := hxall 0
    have huall : ∀ m : ℕ, u ∈ principalUnitSubgroup 𝒪[K] m := by
      intro m
      obtain ⟨v, hv, hvx⟩ := hxall m
      have huv : u = v := by
        apply Units.ext
        apply Subtype.ext
        exact congrArg Units.val (hux.trans hvx.symm)
      exact huv.symm ▸ hv
    have huInf : u ∈ (⨅ m : ℕ, principalUnitSubgroup 𝒪[K] m) :=
      Subgroup.mem_iInf.mpr huall
    rw [i_inf_principal K] at huInf
    have huOne : u = 1 := huInf
    rw [huOne, map_one] at hux
    exact hux.symm
  · exact bot_le

/-- A subgroup lying in every principal-unit subgroup is trivial. -/
theorem bot_principal_field
    (D : Subgroup Kˣ)
    (hD : ∀ m : ℕ, D ≤ principalUnitField K m) :
    D = ⊥ := by
  simpa [familyCore] using core_bot_separating
    (fun _ : Unit ↦ D) (principalUnitField K)
    (fun m ↦ (iInf_le (fun _ : Unit ↦ D) ()).trans (hD m))
    (i_inf_bot K)

/-- **Step III.5.4, literal source conclusion.** The intersection of all
finite abelian local norm groups is trivial.  The proposition itself has no
proof-assumption parameters. -/
def NormCoreFormula : Prop :=
  localNormCore K = ⊥

/-- The literal conclusion is equivalent to the precise principal-unit
separation statement needed after the unramified argument has forced the
core into the local units. -/
theorem core_formula_units :
    NormCoreFormula K ↔
      ∀ m : ℕ, localNormCore K ≤ principalUnitField K m := by
  constructor
  · intro h m
    rw [NormCoreFormula] at h
    rw [h]
    exact bot_le
  · intro h
    exact bot_principal_field K (localNormCore K) h

/-- The exact finite-index refinement of the principal-unit filtration used
in Milne's Step 4.  Such a `V` separates one principal-unit layer after
intersecting with `U_K`. -/
def PrincipalIndexRefinements : Prop :=
  ∀ m : ℕ, ∃ V : Subgroup Kˣ,
    V.FiniteIndex ∧
      localUnitSubgroup K ⊓ V ≤ principalUnitField K m

/-- Milne's Step 4 from its two preceding inputs.  Divisibility places the
core in every finite-index subgroup, canonical unramified norms place it in
`U_K`, and the verified principal-unit separating family then makes it
trivial. -/
theorem core_divisible_refinements
    (hdiv : IDSubgro (localNormCore K))
    (hrefine : PrincipalIndexRefinements K) :
    NormCoreFormula K := by
  apply (core_formula_units K).2
  intro m x hx
  obtain ⟨V, hVfinite, hV⟩ := hrefine m
  letI : V.FiniteIndex := hVfinite
  apply hV
  exact ⟨local_core_subgroup K hx,
    hdiv.le_finiteIndex hx⟩

/-- If each finite-index refinement is itself realized by a finite abelian
norm group, membership in the common norm core supplies the same principal
unit containment directly.  This is the exact norm-realization reduction. -/
theorem core_formula_refinements
    (hrefine : ∀ m : ℕ, ∃ L : FASubext K,
      localUnitSubgroup K ⊓ L.normGroup ≤
        principalUnitField K m) :
    NormCoreFormula K := by
  apply (core_formula_units K).2
  intro m x hx
  obtain ⟨L, hL⟩ := hrefine m
  apply hL
  refine ⟨local_core_subgroup K hx, ?_⟩
  rw [localNormCore, familyCore, Subgroup.mem_iInf] at hx
  exact hx L

end

end Towers.CField.LExist
