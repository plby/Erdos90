import Submission.Group.Edmonton.Polycyclic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Edmonton Notes on Nilpotent Groups: supersoluble groups

This file formalizes Hall's Lemma 1.9(ii).
-/

namespace Submission
namespace Edmonton

open Group
open scoped commutatorElement

universe u

/-- Ambient normality restricts to normality inside any containing subgroup. -/
theorem normal_subgroup
    {G : Type u} [Group G] {K H : Subgroup G}
    (hK : K.Normal) (hK_le_H : K ≤ H) :
    (K.subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hK_le_H]
  intro k h hk _
  exact hK.conj_mem k hk h

/-- The conjugation action of `G` on a normal factor `H / K`. -/
noncomputable def factorConjugationHom
    {G : Type u} [Group G] (H K : Subgroup G)
    (hH : H.Normal) (hK : K.Normal) (hK_le_H : K ≤ H) :
    (let _ : (K.subgroupOf H).Normal := normal_subgroup hK hK_le_H;
      G →* MulAut (H ⧸ K.subgroupOf H)) := by
  letI : H.Normal := hH
  letI : K.Normal := hK
  let K' : Subgroup H := K.subgroupOf H
  letI : K'.Normal := normal_subgroup hK hK_le_H
  letI : MulDistribMulAction G H :=
    MulDistribMulAction.compHom H (MulAut.conjNormal : G →* MulAut H)
  letI : MulAction.QuotientAction G K' := by
    constructor
    intro g a a' haa'
    change (g * (a : G) * g⁻¹)⁻¹ * (g * (a' : G) * g⁻¹) ∈ K
    simpa [mul_assoc] using hK.conj_mem (a⁻¹ * a') haa' g
  let quotientAction : MulAction G (H ⧸ K') := inferInstance
  letI : MulDistribMulAction G (H ⧸ K') :=
    { quotientAction with
      smul_one := by
        intro g
        change ((g • (1 : H) : H) : H ⧸ K') = ((1 : H) : H ⧸ K')
        exact congrArg (fun h : H ↦ (h : H ⧸ K'))
          (show g • (1 : H) = 1 from smul_one g)
      smul_mul := by
        intro g a b
        induction a using QuotientGroup.induction_on with
        | H a =>
            induction b using QuotientGroup.induction_on with
            | H b =>
                change ((g • (a * b) : H) : H ⧸ K') =
                  (((g • a : H) * (g • b : H) : H) : H ⧸ K')
                exact congrArg (fun h : H ↦ (h : H ⧸ K'))
                  (show g • (a * b) = (g • a : H) * (g • b : H) from
                    smul_mul' g a b) }
  exact MulDistribMulAction.toMulAut G (H ⧸ K')

/-- The subgroup of `G` that centralizes the normal factor `H / K`. -/
noncomputable def factorCentralizer
    {G : Type u} [Group G] (H K : Subgroup G)
    (hH : H.Normal) (hK : K.Normal) (hK_le_H : K ≤ H) :
    Subgroup G := by
  letI : (K.subgroupOf H).Normal := normal_subgroup hK hK_le_H
  exact (factorConjugationHom H K hH hK hK_le_H).ker

@[simp]
theorem factor_conjugation_coe
    {G : Type u} [Group G] (H K : Subgroup G)
    (hH : H.Normal) (hK : K.Normal) (hK_le_H : K ≤ H)
    (g : G) (h : H) :
    (let _ : (K.subgroupOf H).Normal := normal_subgroup hK hK_le_H;
      factorConjugationHom H K hH hK hK_le_H g
        (h : H ⧸ K.subgroupOf H) =
      ((⟨g * h.1 * g⁻¹, hH.conj_mem h.1 h.2 g⟩ : H) :
        H ⧸ K.subgroupOf H)) := by
  letI : H.Normal := hH
  letI : K.Normal := hK
  letI : (K.subgroupOf H).Normal := normal_subgroup hK hK_le_H
  rfl

/-- The factor centralizer has finite index because the automorphism group of
a cyclic group is finite. -/
theorem factor_centralizer_index
    {G : Type u} [Group G] {H K : Subgroup G}
    (hH : H.Normal) (hK : K.Normal) (hK_le_H : K ≤ H)
    {x : G} (hx : x ∈ H)
    (hgen : H = Subgroup.closure ((K : Set G) ∪ {x})) :
    (factorCentralizer H K hH hK hK_le_H).FiniteIndex := by
  letI : (K.subgroupOf H).Normal := normal_subgroup hK hK_le_H
  haveI hcyclic : IsCyclic (H ⧸ K.subgroupOf H) :=
    cyclic_subgroup_generated hK_le_H
      (normal_subgroup hK hK_le_H) hx hgen
  letI : Finite (MulAut (H ⧸ K.subgroupOf H)) :=
    Finite.of_equiv ((ZMod (Nat.card (H ⧸ K.subgroupOf H)))ˣ)
      (hcyclic.mulAutMulEquiv (H ⧸ K.subgroupOf H)).symm.toEquiv
  change (factorConjugationHom H K hH hK hK_le_H).ker.FiniteIndex
  infer_instance

/-- The commutator subgroup acts trivially on every cyclic normal factor. -/
theorem commutator_centralizer
    {G : Type u} [Group G] {H K : Subgroup G}
    (hH : H.Normal) (hK : K.Normal) (hK_le_H : K ≤ H)
    {x : G} (hx : x ∈ H)
    (hgen : H = Subgroup.closure ((K : Set G) ∪ {x})) :
    commutator G ≤ factorCentralizer H K hH hK hK_le_H := by
  letI : (K.subgroupOf H).Normal := normal_subgroup hK hK_le_H
  haveI hcyclic : IsCyclic (H ⧸ K.subgroupOf H) :=
    cyclic_subgroup_generated hK_le_H
      (normal_subgroup hK hK_le_H) hx hgen
  letI : CommGroup (MulAut (H ⧸ K.subgroupOf H)) :=
    (hcyclic.mulAutMulEquiv (H ⧸ K.subgroupOf H)).toMonoidHom.commGroupOfInjective
      (hcyclic.mulAutMulEquiv (H ⧸ K.subgroupOf H)).injective
  change commutator G ≤ (factorConjugationHom H K hH hK hK_le_H).ker
  exact Abelianization.commutator_subset_ker _

/-- Elements in the factor centralizer commute with the upper factor modulo
the lower factor. -/
theorem commutator_factor_centralizer
    {G : Type u} [Group G] {H K : Subgroup G}
    (hH : H.Normal) (hK : K.Normal) (hK_le_H : K ≤ H) :
    ⁅H, factorCentralizer H K hH hK hK_le_H⁆ ≤ K := by
  letI : (K.subgroupOf H).Normal := normal_subgroup hK hK_le_H
  rw [Subgroup.commutator_le]
  intro h hh c hc
  rw [← commutatorElement_inv c h]
  apply K.inv_mem
  change c ∈ (factorConjugationHom H K hH hK hK_le_H).ker at hc
  have hcact := DFunLike.congr_fun (MonoidHom.mem_ker.mp hc)
    ((⟨h, hh⟩ : H) : H ⧸ K.subgroupOf H)
  have hq :
      ((⟨c * h * c⁻¹, hH.conj_mem h hh c⟩ : H) :
          H ⧸ K.subgroupOf H) =
        ((⟨h, hh⟩ : H) : H ⧸ K.subgroupOf H) := by
    simpa using hcact
  have hm := QuotientGroup.eq_iff_div_mem.mp hq
  have hmG :
      ((⟨c * h * c⁻¹, hH.conj_mem h hh c⟩ : H) /
        (⟨h, hh⟩ : H)).1 ∈ K := hm
  simpa [div_eq_mul_inv, commutatorElement_def, mul_assoc] using hmG

/-- A finite descending central series represented inductively. -/
inductive FCSeries (G : Type u) [Group G] :
    Subgroup G → Subgroup G → Prop
  | refl (H : Subgroup G) : FCSeries G H H
  | step {H K L : Subgroup G}
      (hK_le_H : K ≤ H)
      (hcentral : ⁅H, (⊤ : Subgroup G)⁆ ≤ K)
      (tail : FCSeries G K L) :
      FCSeries G H L

/-- A finite central series forces a sufficiently late lower-central term
into its endpoint. -/
theorem FCSeries.existslower_centralseries_leendpt
    {G : Type u} [Group G] {H L : Subgroup G}
    (h : FCSeries G H L) :
    ∀ {n : ℕ}, Subgroup.lowerCentralSeries G n ≤ H →
      ∃ m : ℕ, Subgroup.lowerCentralSeries G m ≤ L := by
  intro n hn
  induction h generalizing n with
  | refl => exact ⟨n, hn⟩
  | step _ hcentral _ ih =>
      apply ih (n := n + 1)
      exact (Subgroup.commutator_mono hn le_rfl).trans hcentral

/-- A finite central series from the full group to the trivial subgroup
proves nilpotence. -/
theorem FCSeries.isNilpotent
    {G : Type u} [Group G]
    (h : FCSeries G (⊤ : Subgroup G) (⊥ : Subgroup G)) :
    IsNilpotent G := by
  obtain ⟨n, hn⟩ :=
    h.existslower_centralseries_leendpt (n := 0) le_top
  exact Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n, le_bot_iff.mp hn⟩

/-- A finite central series inside a fixed ambient subgroup `D`, represented
by intersections `D ⊓ H` of ambient-group subgroups. -/
inductive CSWithin
    {G : Type u} [Group G] (D : Subgroup G) :
    Subgroup G → Subgroup G → Prop
  | refl (H : Subgroup G) : CSWithin D H H
  | step {H K L : Subgroup G}
      (hK_le_H : K ≤ H)
      (hcentral : ⁅D ⊓ H, D⁆ ≤ D ⊓ K)
      (tail : CSWithin D K L) :
      CSWithin D H L

/-- Restrict a central series inside `E` to a smaller subgroup `D`. -/
theorem CSWithin.mono
    {G : Type u} [Group G] {D E H L : Subgroup G}
    (hDE : D ≤ E) (h : CSWithin E H L) :
    CSWithin D H L := by
  induction h with
  | refl => exact .refl _
  | @step H K L hK_le_H hcentral _ ih =>
      have hDH : D ⊓ H ≤ E ⊓ H := fun _ hx ↦ ⟨hDE hx.1, hx.2⟩
      have hcentralK : ⁅D ⊓ H, D⁆ ≤ K :=
        (Subgroup.commutator_mono hDH hDE).trans
          hcentral |>.trans inf_le_right
      have hcentralD : ⁅D ⊓ H, D⁆ ≤ D :=
        (Subgroup.commutator_mono inf_le_left le_rfl).trans
          D.commutator_le_self
      exact .step hK_le_H (le_inf hcentralD hcentralK) ih

/-- Turn an ambient intersection series into an ordinary central series of
the subgroup `D`. -/
theorem CSWithin.fin_central_series
    {G : Type u} [Group G] {D H L : Subgroup G}
    (h : CSWithin D H L) :
    FCSeries D (H.subgroupOf D) (L.subgroupOf D) := by
  induction h with
  | refl => exact .refl _
  | @step H K L hK_le_H hcentral _ ih =>
      have hcentralD :
          ⁅H.subgroupOf D, (⊤ : Subgroup D)⁆ ≤ K.subgroupOf D := by
        rw [Subgroup.commutator_le]
        intro a ha b _
        exact (hcentral
          (Subgroup.commutator_mem_commutator ⟨a.2, ha⟩ b.2)).2
      exact .step (fun _ hk ↦ hK_le_H hk) hcentralD ih

/-- Construct the finite-index nilpotent kernel by intersecting the
centralizers of all cyclic factors in a supersoluble series. -/
theorem exists_supersolubleKernel
    {G : Type u} [Group G] {H L : Subgroup G}
    (h : HCSeries G (fun K _ ↦ K.Normal) H L)
    (hH : H.Normal) :
    ∃ D : Subgroup G, D.FiniteIndex ∧ commutator G ≤ D ∧
      CSWithin D H L := by
  induction h with
  | refl =>
      exact ⟨⊤, inferInstance, le_top, .refl _⟩
  | @step H K L hK_le_H hK _ hcyclic tail ih =>
      obtain ⟨E, hEfinite, hcommE, hseriesE⟩ := ih hK
      obtain ⟨x, hx, hgen⟩ := hcyclic
      let C : Subgroup G := factorCentralizer H K hH hK hK_le_H
      let D : Subgroup G := C ⊓ E
      letI : C.FiniteIndex :=
        factor_centralizer_index hH hK hK_le_H hx hgen
      letI : E.FiniteIndex := hEfinite
      have hDfinite : D.FiniteIndex := inferInstance
      have hcommD : commutator G ≤ D := le_inf
        (commutator_centralizer hH hK hK_le_H hx hgen) hcommE
      have hcentral :
          ⁅D ⊓ H, D⁆ ≤ D ⊓ K := by
        apply le_inf
        · exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
            D.commutator_le_self
        · exact (Subgroup.commutator_mono inf_le_right inf_le_left).trans
            (commutator_factor_centralizer hH hK hK_le_H)
      exact ⟨D, hDfinite, hcommD,
        .step hK_le_H hcentral (hseriesE.mono inf_le_right)⟩

/-- Hall, Lemma 1.9(ii): every supersoluble group has a finite-index
nilpotent subgroup containing its commutator subgroup. -/
theorem index_nilpotent_supersoluble {G : Type u} [Group G] :
    IsSupersoluble G →
      ∃ K : Subgroup G, IsNilpotent K ∧ K.FiniteIndex ∧ commutator G ≤ K := by
  intro hsuper
  obtain ⟨K, hKfinite, hcommK, hseriesK⟩ :=
    exists_supersolubleKernel hsuper (inferInstance : (⊤ : Subgroup G).Normal)
  have hcentralK :
      FCSeries K (⊤ : Subgroup K) (⊥ : Subgroup K) := by
    simpa using hseriesK.fin_central_series
  exact ⟨K, hcentralK.isNilpotent, hKfinite, hcommK⟩

end Edmonton
end Submission
