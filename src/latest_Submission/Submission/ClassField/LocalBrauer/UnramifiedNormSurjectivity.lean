import Mathlib.Topology.Algebra.IsOpenUnits
import Submission.NumberTheory.Locals.CompleteDVRHenselian
import Submission.ClassField.UnramifiedCohom.PrincipalUnits
import Submission.ClassField.UnramifiedCohom.UnitsModuloPrincipal
import Submission.ClassField.UnramifiedCohom.FiniteFieldNorms
import Submission.ClassField.UnramifiedCohom.FiniteFieldTraces
import Submission.ClassField.UnramifiedCohom.Approximation
import Submission.ClassField.LocalBrauer.LocalField


/-!
# Norms of units in an unramified local extension

We formalize Milne's successive-approximation proof that the norm on units
of a finite unramified Galois extension of nonarchimedean local fields is
surjective.  The unramified input is expressed by the two standard residue
compatibilities: norm on units modulo first principal units, and trace on
every later principal-unit layer.  Compactness of the source unit group and
the adic topology then turn the finite approximations into an exact norm.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u

open IsLocalRing
open ValuativeRel

private abbrev principalUnits (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [ValuativeRel K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (m : ℕ) : Subgroup 𝒪[K]ˣ :=
  Edmonton.idealUnitSubgroup (maximalIdeal 𝒪[K]) m

/-- Reduction identifies local units modulo first principal units with
residue-field units. -/
noncomputable abbrev localUnitsResidue
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K] :
    𝒪[K]ˣ ⧸ principalUnits K 1 ≃* 𝓀[K]ˣ :=
  UCohom.unitsPrincipalEquiv 𝒪[K]

/-- Every positive successive principal-unit quotient is the additive group
of the residue field. -/
noncomputable abbrev principalUnitsSuccessive
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K] (m : ℕ) (hm : 0 < m) :
    principalUnits K m ⧸
        (principalUnits K (m + 1)).subgroupOf (principalUnits K m) ≃*
      Multiplicative 𝓀[K] :=
  UCohom.principalSuccessiveResidue 𝒪[K]
    (maximalIdeal_isPrincipal_of_isDedekindDomain (R := 𝒪[K]))
    (IsDiscreteValuationRing.not_a_field 𝒪[K]) m hm

set_option maxHeartbeats 500000 in
-- Elaborating the valuative-topology basis through the integer subtype is expensive.
/-- The topology on the valuation-relation integer ring of a local field is
the topology defined by powers of its maximal ideal. -/
private theorem valuative_integer_adic
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K] :
    IsAdic (maximalIdeal 𝒪[K]) := by
  letI : IsDiscreteValuationRing 𝒪[K] :=
    discrete_valuation_ring K
  rw [isAdic_iff]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  constructor
  · intro n
    rw [hπ.maximalIdeal_pow_eq_setOf_le_v_coe_pow]
    have hopen := (valuation K).isOpen_closedBall
      (show (valuation K).restrict ((π : K) ^ n) ≠ 0 by
        simp [hπ.ne_zero])
    rw [← map_pow]
    simpa only [Set.preimage_setOf_eq, Valuation.restrict_le_iff] using
      hopen.preimage continuous_subtype_val
  · intro s hs
    rw [nhds_subtype_eq_comap, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    have ht' : t ∈ nhds (0 : K) := by simpa using ht
    rw [IsValuativeTopology.mem_nhds_zero_iff] at ht'
    obtain ⟨γ, hγ⟩ := ht'
    have hπval : valuation K (π : K) < 1 :=
      Valuation.integer.v_irreducible_lt_one hπ
    obtain ⟨n, hn⟩ : ∃ n : ℕ, valuation K (π : K) ^ n < γ :=
      exists_pow_lt₀ hπval γ
    refine ⟨n, ?_⟩
    intro y hy
    apply hts
    apply hγ
    have hy' : valuation K (y : K) ≤ valuation K (π : K) ^ n := by
      exact (Set.ext_iff.mp
        (hπ.maximalIdeal_pow_eq_setOf_le_v_coe_pow (valuation K) n) y).mp hy
    exact hy'.trans_lt hn

private theorem valuative_integer_nhds
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K] :
    (nhds (1 : 𝒪[K])).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      (fun y : 𝒪[K] ↦ 1 + y) ''
        ((maximalIdeal 𝒪[K]) ^ n : Ideal 𝒪[K]) :=
  (valuative_integer_adic K).hasBasis_nhds 1

/-- Principal-unit subgroups form a neighborhood basis of one in the unit
group of a nonarchimedean local field. -/
theorem principal_eventually_subset
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsNonarchimedeanLocalField K]
    (V : Set 𝒪[K]ˣ) (hV : V ∈ nhds (1 : 𝒪[K]ˣ)) :
    ∃ m : ℕ, (principalUnits K m : Set 𝒪[K]ˣ) ⊆ V := by
  letI : IsDiscreteValuationRing 𝒪[K] :=
    discrete_valuation_ring K
  let I := maximalIdeal 𝒪[K]
  have hbasisRing := valuative_integer_nhds K
  have hbasisOpp := hbasisRing.comap MulOpposite.opHomeomorph.symm
  have hbasisUnits := (hbasisRing.prod hbasisOpp).comap
    (Units.embedProduct 𝒪[K])
  simp only [Homeomorph.comap_nhds_eq, Homeomorph.symm_symm,
    MulOpposite.opHomeomorph_apply, MulOpposite.op_one,
    ← nhds_prod_eq] at hbasisUnits
  have hnhds : nhds (1 : 𝒪[K]ˣ) =
      Filter.comap (Units.embedProduct 𝒪[K])
        (nhds ((1 : 𝒪[K]), (1 : 𝒪[K]ᵐᵒᵖ))) := by
    simpa using
      (Units.isInducing_embedProduct.nhds_eq_comap (1 : 𝒪[K]ˣ))
  rw [← hnhds] at hbasisUnits
  rw [hbasisUnits.mem_iff] at hV
  obtain ⟨⟨m₁, m₂⟩, _hm, hmV⟩ := hV
  refine ⟨max m₁ m₂, ?_⟩
  intro v hv
  apply hmV
  constructor
  · change (v : 𝒪[K]) ∈
      (fun y : 𝒪[K] ↦ 1 + y) '' (I ^ m₁ : Ideal 𝒪[K])
    refine ⟨(v : 𝒪[K]) - 1,
      Ideal.pow_le_pow_right (Nat.le_max_left m₁ m₂) hv, ?_⟩
    simp
  · change ((v⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) ∈
      (fun y : 𝒪[K] ↦ 1 + y) '' (I ^ m₂ : Ideal 𝒪[K])
    have hinv := (principalUnits K (max m₁ m₂)).inv_mem hv
    refine ⟨((v⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1,
      Ideal.pow_le_pow_right (Nat.le_max_right m₁ m₂) hinv, ?_⟩
    simp

variable (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsNonarchimedeanLocalField K] [NontriviallyNormedField L]
  [IsUltrametricDist L] [ValuativeRel L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [IsNonarchimedeanLocalField L]
  [Algebra K L] [Module.Finite K L] [IsGalois K L]
  [Algebra 𝓀[K] 𝓀[L]]

/-- The precise unramified residue data used in Milne's norm argument.
The first identity says that reduction intertwines local and residue norms.
The last field is the generator-free conclusion of trace surjectivity on a
positive principal-unit layer: every error at level `m` can be corrected by
a norm up to level `m + 1`. -/
structure UnramifiedUnitData
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) : Prop where
  principal_mem : ∀ (m : ℕ) (v : 𝒪[L]ˣ),
    v ∈ principalUnits L m → N v ∈ principalUnits K m
  residue_norm : ∀ v : 𝒪[L]ˣ,
    localUnitsResidue K (QuotientGroup.mk (N v)) =
      Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
        (localUnitsResidue L (QuotientGroup.mk v))
  successive_approximation : ∀ (m : ℕ) (_hm : 0 < m)
      (u : principalUnits K m),
    ∃ v : principalUnits L m,
      u.1 / N v.1 ∈ principalUnits K (m + 1)

omit [Algebra K L] [Module.Finite K L] [IsGalois K L] in
/-- Residue norm supplies the first lift and residue trace corrects every
later error, so norms approximate any base unit modulo every principal-unit
layer. -/
theorem approximation_unramified_data
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedUnitData K L N)
    (u : 𝒪[K]ˣ) (n : ℕ) :
    ∃ v : 𝒪[L]ˣ, u / N v ∈ principalUnits K (n + 1) := by
  apply UCohom.approximation_through_filtration
    N (principalUnits K)
  · intro a
    obtain ⟨bbar, hbbar⟩ :=
      UCohom.units_norm_surjective 𝓀[K] 𝓀[L]
        (localUnitsResidue K (QuotientGroup.mk a))
    let q : 𝒪[L]ˣ ⧸ principalUnits L 1 :=
      (localUnitsResidue L).symm bbar
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective q
    refine ⟨b, QuotientGroup.eq_iff_div_mem.mp ?_⟩
    apply (localUnitsResidue K).injective
    calc
      localUnitsResidue K (QuotientGroup.mk a) =
          Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L])) bbar := hbbar.symm
      _ = Units.map (Algebra.norm 𝓀[K] (S := 𝓀[L]))
          (localUnitsResidue L (QuotientGroup.mk b)) := by
        rw [hb]
        simp [q]
      _ = localUnitsResidue K (QuotientGroup.mk (N b)) :=
        (hN.residue_norm b).symm
  · intro n a ha
    let m := n + 1
    have hm : 0 < m := by omega
    obtain ⟨b, hb⟩ :=
      hN.successive_approximation m hm
        (⟨a, ha⟩ : principalUnits K m)
    exact ⟨b.1, hb⟩

omit [Algebra K L] [Module.Finite K L] [IsGalois K L] in
/-- Milne, Proposition III.1.2 for an unramified local extension: the norm
on integer-unit groups is surjective.  Compactness is used only in the last
step, to make the continuous norm image closed. -/
theorem units_unramified_data
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedUnitData K L N)
    (hcontinuous : Continuous N) : Function.Surjective N := by
  intro u
  have huClosure : u ∈ closure (Set.range N) := by
    rw [mem_closure_iff_nhds_one]
    intro V hV
    obtain ⟨m, hmV⟩ := principal_eventually_subset K V hV
    obtain ⟨v, hv⟩ :=
      approximation_unramified_data K L N hN u m
    have hv' : u / N v ∈ principalUnits K m := by
      change ((u / N v : 𝒪[K]ˣ) : 𝒪[K]) - 1 ∈
        (maximalIdeal 𝒪[K]) ^ m
      exact Ideal.pow_le_pow_right (Nat.le_succ m) hv
    refine ⟨N v, ⟨v, rfl⟩, hmV ?_⟩
    have hinv := (principalUnits K m).inv_mem hv'
    simpa [div_eq_mul_inv, mul_comm] using hinv
  have hclosed : IsClosed (Set.range N) :=
    (isCompact_range hcontinuous).isClosed
  rw [hclosed.closure_eq] at huClosure
  exact huClosure

omit [Module.Finite K L] [IsGalois K L] in
/-- The corresponding statement written directly with the field norm.  A
bundled map `N` is used only to record that the field norm preserves integer
units; `hN_eq` identifies its values with `Algebra.norm`. -/
theorem integer_unit_norm
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedUnitData K L N)
    (hcontinuous : Continuous N)
    (hN_eq : ∀ v : 𝒪[L]ˣ,
      (((N v : 𝒪[K]) : K)) = Algebra.norm K (((v : 𝒪[L]) : L)))
    (u : 𝒪[K]ˣ) :
    ∃ v : 𝒪[L]ˣ,
      Algebra.norm K (((v : 𝒪[L]) : L)) = ((u : 𝒪[K]) : K) := by
  obtain ⟨v, hv⟩ :=
    units_unramified_data K L N hN hcontinuous u
  refine ⟨v, ?_⟩
  rw [← hN_eq v, hv]

/-- Bundled hypotheses for applying the theorem to a concrete unramified
extension.  Besides the residue diagrams, this records continuity and that
the bundled unit map really is the field norm. -/
structure UnramifiedLocalData
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) : Prop extends
    UnramifiedUnitData K L N where
  continuous_norm : Continuous N
  coe_norm : ∀ v : 𝒪[L]ˣ,
    (((N v : 𝒪[K]) : K)) = Algebra.norm K (((v : 𝒪[L]) : L))

omit [Module.Finite K L] [IsGalois K L] in
/-- The norm on unit groups of a finite unramified Galois extension of local
fields is surjective, in a form ready for a concrete unramified-data
instance. -/
theorem unramified_units_surjective
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N) :
    Function.Surjective N :=
  units_unramified_data K L N
    hN.toUnramifiedUnitData hN.continuous_norm

omit [Module.Finite K L] [IsGalois K L] in
/-- Direct field-norm form of unit norm-surjectivity for bundled unramified
local norm data. -/
theorem unramified_integer_norm
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (u : 𝒪[K]ˣ) :
    ∃ v : 𝒪[L]ˣ,
      Algebra.norm K (((v : 𝒪[L]) : L)) = ((u : 𝒪[K]) : K) :=
  integer_unit_norm K L N hN.toUnramifiedUnitData
    hN.continuous_norm hN.coe_norm u

end

end Submission.CField.LBrauer
