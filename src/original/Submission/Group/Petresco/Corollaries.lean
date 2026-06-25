import Submission.Group.Petresco.SubgroupFamilies

/-!
# Explicit corollaries in Petresco's paper

This file records results stated in the prose between the numbered
propositions.
-/

namespace Submission
namespace Edmonton
namespace P1954

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

/-- A subgroup is normal as soon as its commutator with the ambient group
is contained in it. -/
lemma normal_commutator_top
    (H : Subgroup G) (hcomm : ⁅H, (⊤ : Subgroup G)⁆ ≤ H) :
    H.Normal := by
  refine ⟨?_⟩
  intro x hx g
  have hc : ⁅g, x⁆ ∈ ⁅(⊤ : Subgroup G), H⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top g) hx
  rw [Subgroup.commutator_comm (⊤ : Subgroup G) H] at hc
  have hprod := H.mul_mem (hcomm hc) hx
  simpa [commutatorElement_def, mul_assoc] using hprod

/-- Petresco's consequence after Proposition 5.5: every subgroup inserted
between two terms of a central chain is normal in the ambient group. -/
theorem between_chain_normal
    {lower middle upper : Subgroup G}
    (hlower : lower ≤ middle) (hupper : middle ≤ upper)
    (hcentral : ⁅upper, (⊤ : Subgroup G)⁆ ≤ lower) :
    middle.Normal := by
  letI : upper.Normal :=
    normal_commutator_top upper
      (hcentral.trans (hlower.trans hupper))
  exact normal_of_le
    (Astar := middle) (A := upper) inferInstance
    (hcentral.trans hlower) hupper

/-- The equality displayed immediately after Proposition 5.6. -/
theorem commutator_left_join (A B : Subgroup G) :
    ⁅A, A ⊔ B⁆ = ⁅A, A⁆ ⊔ ⁅A, B⁆ := by
  apply le_antisymm
  · exact sup_internal_mixed (Astar := A) (A := A) (B := B) le_rfl
  · exact sup_le
      (Subgroup.commutator_mono le_rfl le_sup_left)
      (Subgroup.commutator_mono le_rfl le_sup_right)

/-- **Petresco 4.3, literal product form.** -/
theorem join_commutator_right (A B : Subgroup G) :
    ((A ⊔ B : Subgroup G) : Set G) =
      (A : Set G) * (⁅A, B⁆ : Subgroup G) * (B : Set G) := by
  rw [← sup_commutator_join A B]
  exact coe_sup_set (Astar := A) (Bstar := B) le_rfl le_rfl

/-- The reverse outer order in Petresco 4.3. -/
theorem join_commutator_left (A B : Subgroup G) :
    ((A ⊔ B : Subgroup G) : Set G) =
      (B : Set G) * (⁅A, B⁆ : Subgroup G) * (A : Set G) := by
  simpa [sup_comm, Subgroup.commutator_comm] using
    join_commutator_right B A

private lemma product_abc_join (A B : Subgroup G) :
    ((A ⊔ B : Subgroup G) : Set G) =
      (A : Set G) * (B : Set G) * (⁅A, B⁆ : Subgroup G) := by
  ext x
  constructor
  · intro hx
    rw [join_commutator_right A B] at hx
    obtain ⟨ac, ⟨a, ha, c, hc, rfl⟩, b, hb, rfl⟩ := hx
    have hc' : b⁻¹ * c * b ∈ ⁅A, B⁆ := by
      simpa using
        conjugate_commutator_right
          (B.inv_mem hb) hc
    refine ⟨a * b, ⟨a, ha, b, hb, rfl⟩, b⁻¹ * c * b, hc', ?_⟩
    simp [mul_assoc]
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact (A ⊔ B).mul_mem
      ((A ⊔ B).mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right hb))
      ((Subgroup.commutator_mono le_sup_left le_sup_right).trans
        (A ⊔ B).commutator_le_self hc)

private lemma product_cab_join (A B : Subgroup G) :
    ((A ⊔ B : Subgroup G) : Set G) =
      (⁅A, B⁆ : Subgroup G) * (A : Set G) * (B : Set G) := by
  ext x
  constructor
  · intro hx
    rw [join_commutator_right A B] at hx
    obtain ⟨ac, ⟨a, ha, c, hc, rfl⟩, b, hb, rfl⟩ := hx
    have hc' : a * c * a⁻¹ ∈ ⁅A, B⁆ :=
      conjugate_commutator_left ha hc
    refine ⟨(a * c * a⁻¹) * a,
      ⟨a * c * a⁻¹, hc', a, ha, rfl⟩, b, hb, ?_⟩
    simp [mul_assoc]
  · rintro ⟨ca, ⟨c, hc, a, ha, rfl⟩, b, hb, rfl⟩
    exact (A ⊔ B).mul_mem
      ((A ⊔ B).mul_mem
        ((Subgroup.commutator_mono le_sup_left le_sup_right).trans
          (A ⊔ B).commutator_le_self hc)
        (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_right hb)

private lemma product_bac_join (A B : Subgroup G) :
    ((A ⊔ B : Subgroup G) : Set G) =
      (B : Set G) * (A : Set G) * (⁅A, B⁆ : Subgroup G) := by
  ext x
  constructor
  · intro hx
    rw [join_commutator_left A B] at hx
    obtain ⟨bc, ⟨b, hb, c, hc, rfl⟩, a, ha, rfl⟩ := hx
    have hc' : a⁻¹ * c * a ∈ ⁅A, B⁆ := by
      simpa using
        conjugate_commutator_left
          (A.inv_mem ha) hc
    refine ⟨b * a, ⟨b, hb, a, ha, rfl⟩, a⁻¹ * c * a, hc', ?_⟩
    simp [mul_assoc]
  · rintro ⟨ba, ⟨b, hb, a, ha, rfl⟩, c, hc, rfl⟩
    exact (A ⊔ B).mul_mem
      ((A ⊔ B).mul_mem (Subgroup.mem_sup_right hb)
        (Subgroup.mem_sup_left ha))
      ((Subgroup.commutator_mono le_sup_left le_sup_right).trans
        (A ⊔ B).commutator_le_self hc)

private lemma product_cba_join (A B : Subgroup G) :
    ((A ⊔ B : Subgroup G) : Set G) =
      (⁅A, B⁆ : Subgroup G) * (B : Set G) * (A : Set G) := by
  ext x
  constructor
  · intro hx
    rw [join_commutator_left A B] at hx
    obtain ⟨bc, ⟨b, hb, c, hc, rfl⟩, a, ha, rfl⟩ := hx
    have hc' : b * c * b⁻¹ ∈ ⁅A, B⁆ :=
      conjugate_commutator_right hb hc
    refine ⟨(b * c * b⁻¹) * b,
      ⟨b * c * b⁻¹, hc', b, hb, rfl⟩, a, ha, ?_⟩
    simp [mul_assoc]
  · rintro ⟨cb, ⟨c, hc, b, hb, rfl⟩, a, ha, rfl⟩
    exact (A ⊔ B).mul_mem
      ((A ⊔ B).mul_mem
        ((Subgroup.commutator_mono le_sup_left le_sup_right).trans
          (A ⊔ B).commutator_le_self hc)
        (Subgroup.mem_sup_right hb))
      (Subgroup.mem_sup_left ha)

/-- The "order is immaterial" clause of Petresco 4.3, listing all six
pointwise products. -/
theorem join_all_orders (A B : Subgroup G) :
    ((A ⊔ B : Subgroup G) : Set G) =
        (A : Set G) * (⁅A, B⁆ : Subgroup G) * (B : Set G) ∧
      ((A ⊔ B : Subgroup G) : Set G) =
        (A : Set G) * (B : Set G) * (⁅A, B⁆ : Subgroup G) ∧
      ((A ⊔ B : Subgroup G) : Set G) =
        (⁅A, B⁆ : Subgroup G) * (A : Set G) * (B : Set G) ∧
      ((A ⊔ B : Subgroup G) : Set G) =
        (B : Set G) * (⁅A, B⁆ : Subgroup G) * (A : Set G) ∧
      ((A ⊔ B : Subgroup G) : Set G) =
        (B : Set G) * (A : Set G) * (⁅A, B⁆ : Subgroup G) ∧
      ((A ⊔ B : Subgroup G) : Set G) =
        (⁅A, B⁆ : Subgroup G) * (B : Set G) * (A : Set G) :=
  ⟨join_commutator_right A B,
    product_abc_join A B,
    product_cab_join A B,
    join_commutator_left A B,
    product_bac_join A B,
    product_cba_join A B⟩

/-- The solvability consequence stated after Propositions 6.6--6.7:
an extension of a solvable subgroup by a solvable normal subgroup is
solvable. -/
theorem sup_solvable_normal
    (A B : Subgroup G) [IsSolvable A] [IsSolvable B]
    [(B.subgroupOf (A ⊔ B)).Normal] :
    IsSolvable (A ⊔ B : Subgroup G) := by
  obtain ⟨n, hn⟩ := IsSolvable.solvable (G := A)
  obtain ⟨m, hm⟩ := IsSolvable.solvable (G := B)
  have hnA : ambientDerivedSeries A n = ⊥ := by
    simp [ambientDerivedSeries, hn]
  have hmB : ambientDerivedSeries B m = ⊥ := by
    simp [ambientDerivedSeries, hm]
  have hfirst :
      ambientDerivedSeries (A ⊔ B) n ≤ B := by
    have h := derived_join_sup A B n
    simpa [hnA] using h
  have hfinal :
      ambientDerivedSeries (A ⊔ B) (n + m) = ⊥ := by
    apply le_bot_iff.mp
    rw [← ambient_derived_add (A ⊔ B) n m]
    exact (ambient_derived_mono hfirst m).trans_eq hmB
  refine ⟨⟨n + m, ?_⟩⟩
  apply
    (Subgroup.map_eq_bot_iff_of_injective
      (H := derivedSeries (A ⊔ B : Subgroup G) (n + m))
      (A ⊔ B).subtype_injective).mp
  simpa [ambientDerivedSeries] using hfinal

/-- In particular, the product of two normal solvable subgroups is
solvable. -/
theorem sup_solvable
    (A B : Subgroup G) [IsSolvable A] [IsSolvable B]
    [(A.subgroupOf (A ⊔ B)).Normal]
    [(B.subgroupOf (A ⊔ B)).Normal] :
    IsSolvable (A ⊔ B : Subgroup G) :=
  sup_solvable_normal A B

/-- A normal solvable subgroup, packaged as the predicate used to construct
the solvable radical. -/
def SolvableNormalSubgroup (H : Subgroup G) : Prop :=
  H.Normal ∧ IsSolvable H

private lemma maximal_solvable_subgroup
    [WellFoundedGT (Subgroup G)] :
    ∃ H : Subgroup G, Maximal SolvableNormalSubgroup H := by
  apply exists_maximal_of_wellFoundedGT
  exact
    ⟨(⊥ : Subgroup G),
      (show (⊥ : Subgroup G).Normal from inferInstance),
      (show IsSolvable (⊥ : Subgroup G) from inferInstance)⟩

/-- The solvable radical supplied by the maximal-condition argument
following Petresco 6.7. -/
noncomputable def solvableRadical
    [WellFoundedGT (Subgroup G)] : Subgroup G :=
  Classical.choose
    (maximal_solvable_subgroup (G := G))

lemma solvableRadical_maximal
    [WellFoundedGT (Subgroup G)] :
    Maximal SolvableNormalSubgroup (solvableRadical (G := G)) :=
  Classical.choose_spec
    (maximal_solvable_subgroup (G := G))

theorem solvableRadical_normal
    [WellFoundedGT (Subgroup G)] :
    (solvableRadical (G := G)).Normal :=
  (solvableRadical_maximal (G := G)).prop.1

theorem solvable_radical
    [WellFoundedGT (Subgroup G)] :
    IsSolvable (solvableRadical (G := G)) :=
  (solvableRadical_maximal (G := G)).prop.2

/-- Every normal solvable subgroup lies in the solvable radical. -/
theorem le_solvableRadical
    [WellFoundedGT (Subgroup G)]
    (N : Subgroup G) (hN : N.Normal) [IsSolvable N] :
    N ≤ solvableRadical (G := G) := by
  let R := solvableRadical (G := G)
  have hRnormal : R.Normal := solvableRadical_normal (G := G)
  have hRsolvable : IsSolvable R :=
    solvable_radical (G := G)
  letI : R.Normal := hRnormal
  letI : IsSolvable R := hRsolvable
  letI : N.Normal := hN
  have hsupNormal : (R ⊔ N).Normal := inferInstance
  have hsupSolvable : IsSolvable (R ⊔ N : Subgroup G) :=
    sup_solvable R N
  have heq : R = R ⊔ N :=
    (solvableRadical_maximal (G := G)).eq_of_le
      ⟨hsupNormal, hsupSolvable⟩ le_sup_left
  change N ≤ R
  rw [heq]
  exact le_sup_right

/-- The commutator subgroup is characteristic, as noted at the start of
Section 1. -/
theorem commutatorSubgroup_characteristic :
    (commutator G).Characteristic :=
  inferInstance

end P1954
end Edmonton
end Submission
