import Towers.Group.NilpotentProducts.CyclicProducts
import Towers.Group.NilpotentProducts.HallTrees
import Towers.Group.NilpotentProducts.TameBinomialDivisibility
import Towers.Group.NilpotentProducts.TopWeight
import Towers.Group.NilpotentProducts.RankResidueCover
import Towers.Group.HallBasic.NormalForm

/-!
# Hall-coordinate covers at an arbitrary nilpotency cutoff

This file extracts the part of the proof of Struik's Theorem 3 that does
not use the tame-prime hypothesis.  The free nilpotent truncation maps
onto the corresponding nilpotent product of cyclic groups at every cutoff.
Once the Hall factors are known to be annihilated by their recursive leaf
gcds (the content of Lemma 1), reducing all Hall coordinates modulo those
gcds still gives a surjective cover.
-/

namespace Struik
namespace P1960

open Towers
open Towers.TCTex

universe u

/-- The inverse-generator map from the free nilpotent truncation at an
arbitrary cutoff to the corresponding nilpotent product of cyclic groups. -/
noncomputable def inverseFreeTruncation
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) :
    LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n →*
      NilpotentCyclicProduct order n := by
  let f : FreeGroup (FreeGenerator.{u} t) →*
      NilpotentCyclicProduct order n :=
    FreeGroup.lift fun i =>
      (nilpotentCyclicGenerator order n i.down)⁻¹
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} t)) (n - 1)) f
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries
        (NilpotentCyclicProduct order n) (n - 1) :=
    Subgroup.lowerCentralSeries.map f (n - 1) (Subgroup.mem_map_of_mem f hx)
  simpa [nilpotent_cyclic_bot order n]
    using hxmap

@[simp] theorem inverse_truncation_generator
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (i : FreeGenerator.{u} t) :
    inverseFreeTruncation order n
        (lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) n (FreeGroup.of i)) =
      (nilpotentCyclicGenerator order n i.down)⁻¹ := by
  simp [inverseFreeTruncation]

/-- The canonical cyclic generators generate the nilpotent product at
every cutoff. -/
theorem nilpotent_cyclic_top
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) :
    Subgroup.closure
        (Set.range (nilpotentCyclicGenerator order n)) =
      (⊤ : Subgroup (NilpotentCyclicProduct order n)) := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (Subgroup.lowerCentralSeries (CyclicFreeProduct order) (n - 1)) x
  let q : CyclicFreeProduct order →*
      NilpotentCyclicProduct order n :=
    QuotientGroup.mk'
      (Subgroup.lowerCentralSeries (CyclicFreeProduct order) (n - 1))
  let H : Subgroup (NilpotentCyclicProduct order n) :=
    Subgroup.closure
      (Set.range (nilpotentCyclicGenerator order n))
  change q y ∈ H
  have hy :
      y ∈ H.comap q := by
    apply PresentedGroup.generated_by (cyclicOrderRelators order)
    intro i
    change q (cyclicGenerator order i) ∈ H
    exact Subgroup.subset_closure (Set.mem_range_self i)
  exact hy

/-- The arbitrary-cutoff inverse-generator map is surjective. -/
theorem inverse_truncation_surjective
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) :
    Function.Surjective (inverseFreeTruncation.{u} order n) := by
  let value : FreeGenerator.{u} t →
      NilpotentCyclicProduct order n :=
    fun i => (nilpotentCyclicGenerator order n i.down)⁻¹
  have hclosure :
      Subgroup.closure (Set.range value) = ⊤ := by
    apply top_unique
    rw [← nilpotent_cyclic_top order n]
    refine
      (Subgroup.closure_le
        (Subgroup.closure (Set.range value))).2 ?_
    rintro x ⟨i, rfl⟩
    have hvalue :
        value (ULift.up i) ∈ Subgroup.closure (Set.range value) :=
      Subgroup.subset_closure (Set.mem_range_self (ULift.up i))
    simpa [value] using
      (Subgroup.closure (Set.range value)).inv_mem hvalue
  have hfree :
      Function.Surjective (FreeGroup.lift value) :=
    free_range_top value hclosure
  intro x
  obtain ⟨w, rfl⟩ := hfree x
  refine ⟨lowerCentralTruncation
    (FreeGroup (FreeGenerator.{u} t)) n w, ?_⟩
  rfl

/-- Every element of an arbitrary cyclic nilpotent product is the image of
a canonical Hall product in the free nilpotent truncation. -/
theorem mapped_standard_product
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (x : NilpotentCyclicProduct order n) :
    ∃ e : StandardExponentFamily.{u} t,
      inverseFreeTruncation.{u} order n
          (standardHallProduct t n e) =
        x := by
  obtain ⟨y, rfl⟩ :=
    inverse_truncation_surjective.{u} order n x
  obtain ⟨e, he, _⟩ :=
    unique_hall_coordinates t n y
  exact ⟨e, congrArg (inverseFreeTruncation.{u} order n) he⟩

/-- The recursive leaf gcd of a canonical Hall factor.  The value is
independent of the nilpotency cutoff. -/
noncomputable def generalStandardOrder
    {t r : ℕ} (order : Fin t → ℕ)
    (i : (standardHallFamily.{u} t r).index) : ℕ :=
  hallTreeOrder (fun j : FreeGenerator.{u} t => order j.down)
    (concreteBasicTree i)

theorem general_standard_order
    {t r : ℕ} (order : Fin t → ℕ)
    (i : (standardHallFamily.{u} t r).index) :
    generalStandardOrder order i =
      standardFactorOrder order i :=
  rfl

/-- Positive generator orders give positive recursive Hall-factor orders. -/
theorem general_standard_pos
    {t r : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, 0 < order i)
    (i : (standardHallFamily.{u} t r).index) :
    0 < generalStandardOrder order i :=
  standard_order_pos order horder i

/-- If a canonical Hall factor uses a generator, its recursive factor order
divides the prescribed order of that generator. -/
theorem general_standard_uses
    {t r : ℕ} (order : Fin t → ℕ)
    (i : (standardHallFamily.{u} t r).index)
    (j : FreeGenerator.{u} t)
    (huses : hallTreeUses j (concreteBasicTree i)) :
    generalStandardOrder order i ∣ order j.down :=
  tree_dvd_uses
    (fun k : FreeGenerator.{u} t => order k.down) j huses

/-- The top-weight case of Lemma 1 needs no prime restriction: all
collection errors lie in the defining trivial lower-central term. -/
theorem mapped_general_standard
    {t r : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (hr : r = n - 1)
    (i : (standardHallFamily.{u} t r).index) :
    inverseFreeTruncation.{u} order n
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := n)) ^
        generalStandardOrder order i =
      1 := by
  let value : FreeGenerator.{u} t →
      NilpotentCyclicProduct order n :=
    fun j => (nilpotentCyclicGenerator order n j.down)⁻¹
  have hvalue :
      ∀ j, value j ^ order j.down = 1 := by
    intro j
    simpa [value] using congrArg Inv.inv
      (nilpotent_cyclic_generator
        order n j.down)
  have hnext :
      Subgroup.lowerCentralSeries (NilpotentCyclicProduct order n)
          (concreteBasicTree i).weight =
        ⊥ := by
    rw [concrete_tree_weight, hr]
    exact nilpotent_cyclic_bot order n
  have htree :=
    HallTree.tree_top_weight
      (fun j : FreeGenerator.{u} t => order j.down)
      value hvalue (concreteBasicTree i) hnext
  simpa [generalStandardOrder, value,
    BCWt.freeLowerTruncation,
    freeTruncationValue,
    concrete_basic_word,
    inverseFreeTruncation, CWord.map_eval] using htree

/-- Residue-valued Hall coordinates in all positive weights below `n`. -/
abbrev GeneralHallResidues
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) :=
  ∀ r : Fin (n - 1),
    ∀ i : (standardHallFamily.{u} t (r + 1)).index,
      ZMod (generalStandardOrder order i)

/-- Evaluate one residue-valued Hall weight block in the cyclic nilpotent
product at cutoff `n`. -/
noncomputable def mappedGeneralProduct
    {t : ℕ} (order : Fin t → ℕ) (n r : ℕ)
    (z : ∀ i : (standardHallFamily.{u} t r).index,
      ZMod (generalStandardOrder order i)) :
    NilpotentCyclicProduct order n :=
  ((Finset.univ.sort fun i j :
      (standardHallFamily.{u} t r).index => i ≤ j).map fun i =>
    inverseFreeTruncation.{u} order n
        ((standardHallFamily.{u} t r).commutator i
          |>.freeLowerTruncation (n := n)) ^
      zmodRepresentative (z i)).prod

/-- Evaluate all residue-valued Hall blocks in increasing weight. -/
noncomputable def generalResidueEval
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) :
    GeneralHallResidues.{u} order n →
      NilpotentCyclicProduct order n :=
  fun z =>
    ((List.range (n - 1)).attach.map fun r =>
      mappedGeneralProduct order n (r.1 + 1)
        (z ⟨r.1, List.mem_range.mp r.2⟩)).prod

/-- Lemma 1 in precisely the form needed to reduce Hall exponents in the
arbitrary-cutoff cover. -/
def FactorOrderBound
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (_hr : 1 ≤ r) (_hrn : r < n)
    (i : (standardHallFamily.{u} t r).index),
    inverseFreeTruncation.{u} order n
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := n)) ^
        generalStandardOrder order i =
      1

/-- The class-three Lemma 1 already proved for Theorems 1 and 2 is the
cutoff-four instance of the general Hall-factor order bound. -/
theorem order_bound_four
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    FactorOrderBound.{u} order 4 := by
  intro r _hr _hrn i
  simpa [inverseFreeTruncation, inverseTruncation,
    generalStandardOrder] using
      (mapped_standard_order
        order horder i)

theorem mapped_general_cast
    {t : ℕ} (order : Fin t → ℕ) (n r : ℕ)
    (hbound : FactorOrderBound.{u} order n)
    (hr : 1 ≤ r) (hrn : r < n)
    (e : (standardHallFamily.{u} t r).index → ℤ) :
    mappedGeneralProduct order n r
        (fun i =>
          (e i : ZMod (generalStandardOrder order i))) =
      inverseFreeTruncation.{u} order n
        ((standardHallFamily.{u} t r).collectedWeightProduct
          (n := n) e) := by
  unfold mappedGeneralProduct
  rw [BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    SubmonoidClass.coe_list_prod, map_list_prod]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  change
    inverseFreeTruncation.{u} order n
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := n)) ^
        zmodRepresentative
          (e i : ZMod (generalStandardOrder order i)) =
      inverseFreeTruncation.{u} order n
        (((standardHallFamily.{u} t r).commutator i
          |>.freeLowerTruncation (n := n)) ^ e i)
  rw [map_zpow]
  apply zpow_mod_pow
  · exact
      (ZMod.intCast_eq_intCast_iff
        (zmodRepresentative
          (e i : ZMod (generalStandardOrder order i)))
        (e i) (generalStandardOrder order i)).mp
        (zmodRepresentative_cast
          (e i : ZMod (generalStandardOrder order i)))
  · exact hbound r hr hrn i

set_option maxHeartbeats 800000 in
-- Expanding all Hall weight blocks and their mapped products is elaboration-heavy.
/-- Assuming Lemma 1's Hall-factor order bound, reducing every Hall
coordinate modulo its recursive leaf gcd remains surjective. -/
theorem general_surjective_bound
    {t : ℕ} (order : Fin t → ℕ) (n : ℕ)
    (hbound : FactorOrderBound.{u} order n) :
    Function.Surjective (generalResidueEval.{u} order n) := by
  intro x
  obtain ⟨e, he⟩ :=
    mapped_standard_product.{u} order n x
  let z : GeneralHallResidues.{u} order n :=
    fun r i =>
      (e (r + 1) i :
        ZMod (generalStandardOrder order i))
  refine ⟨z, ?_⟩
  unfold generalResidueEval
  rw [show
      ((List.range (n - 1)).attach.map fun r =>
        mappedGeneralProduct order n (r.1 + 1)
          (z ⟨r.1, List.mem_range.mp r.2⟩)).prod =
        ((List.range (n - 1)).attach.map fun r =>
          inverseFreeTruncation.{u} order n
            ((standardHallFamily.{u} t (r.1 + 1)).collectedWeightProduct
              (n := n) (e (r.1 + 1)))).prod by
      apply congrArg List.prod
      apply List.map_congr_left
      intro r hr
      apply mapped_general_cast
        order n (r.1 + 1) hbound
      · omega
      · have hrlt : r.1 < n - 1 := List.mem_range.mp r.2
        omega]
  let factors : ℕ →
      LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) n :=
    fun r =>
      (standardHallFamily.{u} t (r + 1)).collectedWeightProduct
        (n := n) (e (r + 1))
  let mappedFactors : ℕ → NilpotentCyclicProduct order n :=
    fun r => inverseFreeTruncation.{u} order n (factors r)
  change
    ((List.range (n - 1)).attach.map fun r =>
      mappedFactors r.1).prod = x
  rw [show
      ((List.range (n - 1)).attach.map fun r =>
        mappedFactors r.1).prod =
        ((List.range (n - 1)).map mappedFactors).prod by
      exact congrArg List.prod
        (List.attach_map_val
          (l := List.range (n - 1)) (f := mappedFactors))]
  calc
    ((List.range (n - 1)).map mappedFactors).prod =
        inverseFreeTruncation.{u} order n
          (((List.range (n - 1)).map factors).prod) := by
      simpa [mappedFactors] using
        (map_list_prod (inverseFreeTruncation.{u} order n)
          ((List.range (n - 1)).map factors)).symm
    _ = inverseFreeTruncation.{u} order n
          (standardHallProduct t n e) := by
      rfl
    _ = x := he

end P1960
end Struik
