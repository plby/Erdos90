import Towers.ClassField.NormCorrespondence.Main
import Towers.ClassField.NormCorrespondence.ExistenceConsequences
import Towers.ClassField.NormCorrespondence.UnramifiedNormGroups
import Towers.ClassField.LocalExistence.FinalCompactness
import Towers.ClassField.LocalExistence.ValuationClassification
import Towers.ClassField.LocalExistence.FinalGroupArgument

/-!
# Concrete reduction of the local existence theorem

This file connects the abstract final argument of Chapter III, Section 5 to
the norm groups of finite abelian subextensions used in the statement of the
Local Existence Theorem.
-/

namespace Towers.CField.LExist

open Towers.CField.LFTheory
open Towers.CField.LBrauer

noncomputable section

universe u

variable (K : Type u) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

/-- The family of norm subgroups of all finite abelian subextensions in the
fixed separable closure. -/
def localNormFamily (L : FASubext K) : Subgroup Kˣ :=
  L.normGroup

/-- The common norm subgroup of all finite abelian subextensions. -/
def localNormCore : Subgroup Kˣ :=
  familyCore (localNormFamily K)

/-- An element which is a norm from every finite abelian extension is a
local unit.  It is enough to test against the canonical unramified
extensions: its normalized order is then divisible by every positive
integer, hence is zero. -/
theorem local_core_subgroup :
    localNormCore K ≤ localUnitSubgroup K := by
  intro x hx
  apply (local_subgroup K x).2
  have hxnorm (n : ℕ) :
      x ∈ (canonicalUnramifiedSubextension K (n + 1)).normGroup := by
    rw [localNormCore, familyCore, Subgroup.mem_iInf] at hx
    exact hx (canonicalUnramifiedSubextension K (n + 1))
  let z : ℤ := localUnitOrder K (Additive.ofMul x)
  have hdiv (n : ℕ) : ((n + 1 : ℕ) : ℤ) ∣ z := by
    letI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
    apply (mod_ker_dvd K (n + 1) x).1
    rw [← unramified_subextension_ker]
    exact hxnorm n
  have hz : z = 0 := by
    by_contra hz
    have hdvd : ((z.natAbs + 1 : ℕ) : ℤ) ∣ z := hdiv z.natAbs
    have hle : ((z.natAbs + 1 : ℕ) : ℤ) ≤ |z| :=
      Int.le_abs_of_dvd hz hdvd
    rw [Nat.cast_add, Nat.cast_one, Int.natCast_natAbs] at hle
    omega
  apply le_antisymm
  · have hle : localUnitOrder K (Additive.ofMul (1 : Kˣ)) ≤
        localUnitOrder K (Additive.ofMul x) := by
      simp [z, hz]
    simpa using
      (local_order_valuation K (1 : Kˣ) x).1 hle
  · have hle : localUnitOrder K (Additive.ofMul x) ≤
        localUnitOrder K (Additive.ofMul (1 : Kˣ)) := by
      simp [z, hz]
    simpa using
      (local_order_valuation K x (1 : Kˣ)).1 hle

/-- A finite-index subgroup containing the local units is the norm group of
a canonical unramified extension.  This is the concrete Step III.5.5 input. -/
theorem local_unit_subgroup
    (I : Subgroup Kˣ) [I.FiniteIndex]
    (hUI : localUnitSubgroup K ≤ I) :
    LGroup K I := by
  have hker : (localUnitOrder K).ker ≤ I.toAddSubgroup := by
    intro x hx
    change x.toMul ∈ I
    apply hUI
    apply (local_subgroup K x.toMul).2
    have hxorder : localUnitOrder K x = 0 := hx
    have hone : localUnitOrder K (Additive.ofMul (1 : Kˣ)) = 0 :=
      map_zero (localUnitOrder K)
    apply le_antisymm
    · have hle : localUnitOrder K (Additive.ofMul (1 : Kˣ)) ≤
      localUnitOrder K x := by simp [hxorder]
      simpa using
        (local_order_valuation K (1 : Kˣ) x.toMul).1 hle
    · have hle : localUnitOrder K x ≤
          localUnitOrder K (Additive.ofMul (1 : Kˣ)) := by
        simp [hxorder]
      simpa using
        (local_order_valuation K x.toMul (1 : Kˣ)).1 hle
  letI : I.toAddSubgroup.FiniteIndex :=
    (Subgroup.finiteIndex_toAddSubgroup_iff (H := I)).2 inferInstance
  obtain ⟨n, hn, hI⟩ :=
    comap_zmultiples_ker
      (localUnitOrder K) (local_order_surjective K)
      I.toAddSubgroup hker
  letI : NeZero n := ⟨hn⟩
  have hsubgroup : I = (localOrderMod K n).ker := by
    ext x
    change Additive.ofMul x ∈ I.toAddSubgroup ↔
      x ∈ (localOrderMod K n).ker
    rw [hI, mod_ker_dvd]
    change localUnitOrder K (Additive.ofMul x) ∈
        AddSubgroup.zmultiples (n : ℤ) ↔ _
    rw [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [smul_eq_mul, mul_comm] using hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [smul_eq_mul, mul_comm] using hk.symm⟩
  rw [hsubgroup]
  exact local_mod_group K n

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The local unit subgroup is compact. -/
theorem local_unit_compact :
    IsCompact (localUnitSubgroup K : Set Kˣ) := by
  let f : (Valuation.integer (ValuativeRel.valuation K))ˣ → Kˣ :=
    fun u ↦ ((integerUnitLocal K u : localUnitSubgroup K) : Kˣ)
  have hcontinuous : Continuous f :=
    continuous_subtype_val.comp (continuous_integer_local K)
  have hrange : Set.range f = (localUnitSubgroup K : Set Kˣ) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact (integerUnitLocal K u).property
    · intro hx
      let y : localUnitSubgroup K := ⟨x, hx⟩
      refine ⟨localInteger K y, ?_⟩
      apply Units.ext
      rfl
  rw [← hrange]
  simpa only [Set.image_univ] using isCompact_univ.image hcontinuous

/-- Under local reciprocity, every member of the finite-abelian norm family
is closed. -/
theorem family_closed_reciprocity
    (hrec : LocalReciprocityLaw K) (L : FASubext K) :
    IsClosed (localNormFamily K L : Set Kˣ) := by
  apply (localNormFamily K L).isClosed_of_isOpen
  exact (L.normgr_openf_indel K hrec).1

omit [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- The compositum clause of the local norm correspondence makes the family
of finite-abelian norm groups downward directed. -/
theorem local_family_directed
    (hNorm : LocalNormCorrespondence K)
    (L₁ L₂ : FASubext K) :
    ∃ M : FASubext K,
      localNormFamily K M ≤ localNormFamily K L₁ ⊓ localNormFamily K L₂ := by
  obtain ⟨M, _, hM⟩ := hNorm.norm_compositum L₁ L₂
  exact ⟨M, le_of_eq hM⟩

/-- The reverse implication in the Local Existence Theorem follows from the
three arithmetic inputs isolated by Milne's Chapter III proof: local
reciprocity, the local norm correspondence, and divisibility of the common
finite-abelian norm subgroup. -/
theorem existence_correspondence_divisible
    (hrec : LocalReciprocityLaw K)
    (hNorm : LocalNormCorrespondence K)
    (hdiv : IDSubgro (localNormCore K)) :
    ∀ I : Subgroup Kˣ,
      OFSubgro I → LGroup K I := by
  intro I hI
  letI : I.FiniteIndex := hI.2
  letI : Nonempty (FASubext K) :=
    ⟨canonicalUnramifiedSubextension K 1⟩
  have hcore : localNormCore K ≤ I := hdiv.le_finiteIndex
  obtain ⟨L, hLI⟩ := inf_directed_core
    (localUnitSubgroup K) I (localNormFamily K)
    (local_unit_compact K) hI.1
    (family_closed_reciprocity K hrec)
    (local_family_directed K hNorm) hcore
  refine family_inf
    (LGroup K) (localUnitSubgroup K) I
    ?_ ?_ ?_ ?_ (localNormFamily K L) ⟨L, rfl⟩ hLI
  · intro N hN
    exact hN.fin_index_localrecipro K hrec
  · intro N J hN hNJ hJfinite
    rcases hN with ⟨E, hE⟩
    apply hNorm.supergroup_norm_group E J
    exact hE.trans_le hNJ
  · intro N₁ N₂ hN₁ hN₂
    rcases hN₁ with ⟨E₁, rfl⟩
    rcases hN₂ with ⟨E₂, rfl⟩
    obtain ⟨M, _, hM⟩ := hNorm.norm_compositum E₁ E₂
    exact ⟨M.normGroup, ⟨M, rfl⟩, le_of_eq hM⟩
  · intro J hJfinite hUJ
    letI : J.FiniteIndex := hJfinite
    exact local_unit_subgroup K J hUJ

/-- A precise conditional form of Theorem I.1.4 exposing the remaining
arithmetic inputs of Milne's proof. -/
theorem correspondence_divisible_core
    (hrec : LocalReciprocityLaw K)
    (hNorm : LocalNormCorrespondence K)
    (hdiv : IDSubgro (localNormCore K)) :
    LocalExistenceTheorem K := by
  intro I
  constructor
  · exact local_existence_reciprocity K hrec I
  · exact existence_correspondence_divisible
      K hrec hNorm hdiv I

/-- Corollary I.1.2 supplies the norm-correspondence input, so after local
reciprocity the only remaining arithmetic input in Milne's existence proof
is divisibility of the common norm subgroup. -/
theorem existence_reciprocity_divisible
    (hrec : LocalReciprocityLaw K)
    (hdiv : IDSubgro (localNormCore K)) :
    LocalExistenceTheorem K :=
  correspondence_divisible_core
    K hrec (norm_correspondence_reciprocity hrec) hdiv

end

end Towers.CField.LExist
