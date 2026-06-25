import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.NumberTheory.LocalField.Basic
import Towers.ClassField.LocalFields.NormSubgroups
import Towers.ClassField.LocalBrauer.FiniteExtensionNorm


/-!
# Class Field Theory, Chapter I, Lemma 1.3

This file formalizes Milne's proof that a finite-index norm group is open.
It first isolates the topological-group argument, then supplies all of its
arithmetic inputs for a finite Galois extension of nonarchimedean local
fields with the canonical spectral topology.
-/

namespace Towers.CField.LFTheory

open Set

section

variable {G A : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The topological core of Lemma 1.3.  If `H` has finite index and its
intersection with an open subgroup `U` is closed in `U`, then `H` is open. -/
theorem subgroup_open_closed
    (H U : Subgroup G) [H.FiniteIndex] (hU : IsOpen (U : Set G))
    (hclosed : IsClosed (H.subgroupOf U : Set U)) :
    IsOpen (H : Set G) := by
  let HU : Subgroup U := H.subgroupOf U
  haveI : HU.FiniteIndex := inferInstance
  have hHUOpen : IsOpen (HU : Set U) :=
    HU.isOpen_of_isClosed_of_finiteIndex hclosed
  have hmapOpen : IsOpen (HU.map U.subtype : Set G) := by
    rw [Subgroup.coe_map]
    exact hU.isOpenMap_subtype_val _ hHUOpen
  apply Subgroup.isOpen_mono (H₁ := HU.map U.subtype) (H₂ := H) ?_ hmapOpen
  rintro _ ⟨u, hu, rfl⟩
  exact hu

/-- Milne's compact-unit argument.  A continuous homomorphism from a compact
group has closed range; if that range is `H ∩ U` inside an open subgroup `U`,
then the finite-index subgroup `H` is open. -/
theorem open_compact_range
    [T2Space G] [Group A] [TopologicalSpace A] [CompactSpace A]
    (H U : Subgroup G) [H.FiniteIndex] (hU : IsOpen (U : Set G))
    (f : A →* U) (hf : Continuous f)
    (hrange : f.range = H.subgroupOf U) :
    IsOpen (H : Set G) := by
  apply subgroup_open_closed H U hU
  rw [← hrange, MonoidHom.coe_range]
  simpa only [Set.image_univ] using (isCompact_univ.image hf).isClosed

end

section LocalFieldUnits

open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K]

/-- The unit subgroup `U_K` of a nonarchimedean local field, viewed inside
`K^x`: its elements are exactly those of valuation one. -/
noncomputable def localUnitSubgroup : Subgroup Kˣ :=
  ((valuation K).toMonoidWithZeroHom.toMonoidHom.comp (Units.coeHom K)).ker

@[simp]
theorem local_subgroup (u : Kˣ) :
    u ∈ localUnitSubgroup K ↔ valuation K (u : K) = 1 :=
  Iff.rfl

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The base-field unit subgroup is open in `K^x`, as used at the end of the
proof of Lemma 1.3. -/
theorem local_unit_open : IsOpen (localUnitSubgroup K : Set Kˣ) := by
  change IsOpen {u : Kˣ | valuation K (u : K) = 1}
  let v := valuation K
  let e := ValueGroupWithZero.orderMonoidIso v
  have heq (x : K) : v.restrict x = e 1 ↔ valuation K x = 1 := by
    constructor
    · intro h
      have hcanonical : e (valuation K x) = v.restrict x := by
        rw [v.restrict_def]
        exact ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀ v x
      exact e.injective (hcanonical.trans h)
    · intro h
      rw [v.restrict_def, ← ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀ v x, h]
  have hr : e 1 ≠ 0 := by simp [e]
  have hopen : IsOpen {x : K | valuation K x = 1} := by
    convert v.isOpen_sphere hr using 1
    ext x
    exact (heq x).symm
  exact hopen.preimage Units.continuous_val

end LocalFieldUnits

section NormGroups

open ValuativeRel

variable (K L A : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [T2Space K] [Ring L] [Algebra K L]
  [Group A] [TopologicalSpace A] [CompactSpace A]

/-- **Lemma 1.3, compact-unit form.** Suppose the norm on local units is
realized by a continuous homomorphism from a compact group and its range is
the intersection of the full norm group with `U_K`.  If the full norm group
has finite index, then it is open.

For a finite extension of local fields, Milne takes `A = U_L`.  Compactness
and the topological argument are unconditional here; constructing the
valuation-compatible norm map and proving the displayed range equality are
the remaining local-extension inputs.
-/
theorem open_compact_unit
    [(normSubgroup K L).FiniteIndex]
    (unitNorm : A →* localUnitSubgroup K) (hcontinuous : Continuous unitNorm)
    (hrange : unitNorm.range =
      (normSubgroup K L).subgroupOf (localUnitSubgroup K)) :
    IsOpen (normSubgroup K L : Set Kˣ) := by
  exact open_compact_range
    (normSubgroup K L) (localUnitSubgroup K)
      (local_unit_open K) unitNorm hcontinuous hrange

end NormGroups

section FLExt

open Towers.CField.LBrauer
open ValuativeRel

noncomputable section

universe u v

variable (K : Type u) (L : Type v)
  [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [Field L] [Algebra K L] [Module.Finite K L] [IsGalois K L]

omit [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- For the canonical spectral norm on a finite Galois extension, the norm
of an element has absolute value equal to the extension degree power of the
element's absolute value. -/
theorem fieldNorm_nnnorm (x : L) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      LBrauer.FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    ‖Algebra.norm K x‖₊ = ‖x‖₊ ^ Module.finrank K L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    LBrauer.FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  calc
    ‖Algebra.norm K x‖₊ =
        ‖algebraMap K L (Algebra.norm K x)‖₊ := by
      apply NNReal.eq
      simp
    _ = ‖∏ σ : Gal(L/K), σ x‖₊ := by
      rw [Algebra.norm_eq_prod_automorphisms]
    _ = ∏ σ : Gal(L/K), ‖σ x‖₊ := by simp
    _ = ∏ _σ : Gal(L/K), ‖x‖₊ := by
      apply Finset.prod_congr rfl
      intro σ _
      apply NNReal.eq
      exact spectralNorm_eq_of_equiv σ x |>.symm
    _ = ‖x‖₊ ^ Module.finrank K L := by
      rw [Finset.prod_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

/-- A field norm is a base-field unit exactly when its preimage is an
extension-field unit.  This is the equality of valuations used in Milne's
proof of Lemma 1.3. -/
theorem field_unit_subgroup (x : Lˣ) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      LBrauer.FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L :=
      LBrauer.FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    normOnUnits K L x ∈ localUnitSubgroup K ↔
      x ∈ localUnitSubgroup L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    LBrauer.FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    LBrauer.FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  change valuation K (Algebra.norm K (x : L)) = 1 ↔
    valuation L (x : L) = 1
  rw [(ValuativeRel.isEquiv (valuation K)
      (NormedField.valuation (K := K))).eq_one_iff_eq_one,
    (ValuativeRel.isEquiv (valuation L)
      (NormedField.valuation (K := L))).eq_one_iff_eq_one]
  simp only [NormedField.valuation_apply]
  rw [fieldNorm_nnnorm K L]
  exact pow_eq_one_iff_of_nonneg zero_le
    Module.finrank_pos.ne'

/-- An integer-ring unit, viewed as an element of the local unit subgroup of
the fraction field. -/
noncomputable def integerUnitLocal
    (F : Type*) [Field F] [ValuativeRel F] :
    (Valuation.integer (valuation F))ˣ →* localUnitSubgroup F :=
  (Units.map (Valuation.integer (valuation F)).subtype.toMonoidHom).codRestrict
    (localUnitSubgroup F) fun u ↦ by
      change valuation F ((((u : (Valuation.integer (valuation F))ˣ) :
        Valuation.integer (valuation F)) : F)) = 1
      exact (Valuation.integer.integers (valuation F)).valuation_unit u

@[simp]
theorem integer_unit_coe
    (F : Type*) [Field F] [ValuativeRel F]
    (u : (Valuation.integer (valuation F))ˣ) :
    (((integerUnitLocal F u : localUnitSubgroup F) : Fˣ) : F) =
      ((u : Valuation.integer (valuation F)) : F) := rfl

/-- The inclusion of integer-ring units into local field units is
continuous. -/
theorem continuous_integer_local
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] :
    Continuous (integerUnitLocal F) := by
  exact (continuous_subtype_val.units_map).subtype_mk _

/-- A local field unit, viewed as a unit of its valuation integer ring. -/
noncomputable def localInteger
    (F : Type*) [Field F] [ValuativeRel F] :
    localUnitSubgroup F →* (Valuation.integer (valuation F))ˣ where
  toFun x :=
    { val := ⟨((x : Fˣ) : F), x.property.le⟩
      inv := ⟨(((x : Fˣ)⁻¹ : Fˣ) : F), by
        rw [Valuation.mem_integer_iff]
        simpa using ((valuation F).val_eq_one_iff.mp x.property).le⟩
      val_inv := by ext; simp
      inv_val := by ext; simp }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
theorem local_integer_coe
    (F : Type*) [Field F] [ValuativeRel F]
    (x : localUnitSubgroup F) :
    (((localInteger F x :
      (Valuation.integer (valuation F))ˣ) :
        Valuation.integer (valuation F)) : F) = ((x : Fˣ) : F) := rfl

/-- The local unit subgroup of a nonarchimedean local field is compact.
It is the continuous image of the compact unit group of the valuation
integer ring. -/
theorem local_unit_compact
    (F : Type*) [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsCompact (localUnitSubgroup F : Set Fˣ) := by
  let f : (Valuation.integer (valuation F))ˣ → Fˣ :=
    fun u ↦ ((integerUnitLocal F u : localUnitSubgroup F) : Fˣ)
  have hcontinuous : Continuous f :=
    continuous_subtype_val.comp (continuous_integer_local F)
  have hrange : Set.range f = (localUnitSubgroup F : Set Fˣ) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact (integerUnitLocal F u).property
    · intro hx
      let y : localUnitSubgroup F := ⟨x, hx⟩
      refine ⟨localInteger F y, ?_⟩
      apply Units.ext
      rfl
  rw [← hrange]
  simpa only [Set.image_univ] using isCompact_univ.image hcontinuous

/-- The norm on integer units, with codomain presented as the base local
unit subgroup. -/
noncomputable def compactUnitNorm :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      LBrauer.FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L :=
      LBrauer.FLExt.valuativeRel K L
    (Valuation.integer (valuation L))ˣ →* localUnitSubgroup K := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    LBrauer.FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    LBrauer.FLExt.valuativeRel K L
  exact (integerUnitLocal K).comp
    (LBrauer.FLExt.integerUnitNorm K L)

/-- The norm on the compact integer-unit group is continuous. -/
theorem continuous_compact_norm :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      LBrauer.FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L :=
      LBrauer.FLExt.valuativeRel K L
    Continuous (compactUnitNorm K L) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    LBrauer.FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    LBrauer.FLExt.valuativeRel K L
  exact (continuous_integer_local K).comp
    (LBrauer.FLExt.continuous_integer_norm K L)

/-- The image of the norm on extension units is precisely the intersection
of the full norm group with the base unit subgroup. -/
theorem compact_unit_range :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      LBrauer.FLExt.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel L :=
      LBrauer.FLExt.valuativeRel K L
    letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
    (compactUnitNorm K L).range =
      (normSubgroup K L).subgroupOf (localUnitSubgroup K) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    LBrauer.FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    LBrauer.FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    change (compactUnitNorm K L u : Kˣ) ∈ normSubgroup K L
    refine ⟨Units.map
      (Valuation.integer (valuation L)).subtype.toMonoidHom u, ?_⟩
    rfl
  · intro hz
    change (z : Kˣ) ∈ normSubgroup K L at hz
    rcases hz with ⟨y, hy⟩
    have hyunit : y ∈ localUnitSubgroup L := by
      apply (field_unit_subgroup K L y).mp
      rw [hy]
      exact z.property
    refine ⟨localInteger L ⟨y, hyunit⟩, ?_⟩
    apply Subtype.ext
    exact hy

/-- **CFT I, Lemma 1.3.** A finite-index norm subgroup from a finite Galois
extension of nonarchimedean local fields is open. -/
theorem norm_subgroup
    [(normSubgroup K L).FiniteIndex] :
    IsOpen (normSubgroup K L : Set Kˣ) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    LBrauer.FLExt.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel L :=
    LBrauer.FLExt.valuativeRel K L
  letI : Valuation.Compatible (NormedField.valuation (K := L)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := L))
  letI : IsNonarchimedeanLocalField L :=
    LBrauer.FLExt.nonarchimedeanLocalField K L
  exact open_compact_unit K L
    ((Valuation.integer (valuation L))ˣ)
    (compactUnitNorm K L) (continuous_compact_norm K L)
    (compact_unit_range K L)

end

end FLExt

end Towers.CField.LFTheory
