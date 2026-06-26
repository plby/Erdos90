import Submission.Group.NilpotentProducts.CyclicProducts
import Submission.Group.NilpotentProducts.HallTrees
import Submission.Group.HallBasic.NormalForm

/-!
# The free class-three truncation maps onto the cyclic nilpotent product

The map used below sends a free generator to the inverse of the corresponding
cyclic generator.  With this choice, Mathlib's commutator convention on the
canonical Hall trees becomes Hall's convention used by Struik.
-/

namespace Struik
namespace P1960

open Submission
open Submission.TCTex
open Submission.TCTex

universe u

/-- The inverse-generator map from the free class-three truncation onto
Struik's fourth nilpotent product. -/
noncomputable def inverseTruncation
    {t : ℕ} (order : Fin t → ℕ) :
    LowerCentralTruncation
        (FreeGroup (FreeGenerator.{u} t)) 4 →*
      NilpotentCyclicProduct order 4 := by
  let f : FreeGroup (FreeGenerator.{u} t) →*
      NilpotentCyclicProduct order 4 :=
    FreeGroup.lift fun i =>
      (nilpotentCyclicGenerator order 4 i.down)⁻¹
  apply QuotientGroup.lift
    (Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} t)) 3) f
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have hxmap :
      f x ∈ Subgroup.lowerCentralSeries
        (NilpotentCyclicProduct order 4) 3 :=
    Subgroup.lowerCentralSeries.map f 3 (Subgroup.mem_map_of_mem f hx)
  simpa [nilpotent_four_bot order]
    using hxmap

@[simp] theorem free_truncation_generator
    {t : ℕ} (order : Fin t → ℕ)
    (i : FreeGenerator.{u} t) :
    inverseTruncation order
        (lowerCentralTruncation
          (FreeGroup (FreeGenerator.{u} t)) 4 (FreeGroup.of i)) =
      (nilpotentCyclicGenerator order 4 i.down)⁻¹ := by
  simp [inverseTruncation]

/-- The canonical cyclic generators generate every nilpotent cyclic
product. -/
theorem range_nilpotent_top
    {t : ℕ} (order : Fin t → ℕ) :
    Subgroup.closure
        (Set.range (nilpotentCyclicGenerator order 4)) =
      (⊤ : Subgroup (NilpotentCyclicProduct order 4)) := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (Subgroup.lowerCentralSeries (CyclicFreeProduct order) 3) x
  let q : CyclicFreeProduct order →*
      NilpotentCyclicProduct order 4 :=
    QuotientGroup.mk'
      (Subgroup.lowerCentralSeries (CyclicFreeProduct order) 3)
  let H : Subgroup (NilpotentCyclicProduct order 4) :=
    Subgroup.closure
      (Set.range (nilpotentCyclicGenerator order 4))
  change q y ∈ H
  have hy :
      y ∈ H.comap q := by
    apply PresentedGroup.generated_by (cyclicOrderRelators order)
    intro i
    change q (cyclicGenerator order i) ∈ H
    exact Subgroup.subset_closure (Set.mem_range_self i)
  exact hy

/-- The inverse-generator map is surjective. -/
theorem free_truncation_surjective
    {t : ℕ} (order : Fin t → ℕ) :
    Function.Surjective (inverseTruncation.{u} order) := by
  let value : FreeGenerator.{u} t →
      NilpotentCyclicProduct order 4 :=
    fun i => (nilpotentCyclicGenerator order 4 i.down)⁻¹
  have hclosure :
      Subgroup.closure (Set.range value) = ⊤ := by
    apply top_unique
    rw [← range_nilpotent_top order]
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
    (FreeGroup (FreeGenerator.{u} t)) 4 w, ?_⟩
  rfl

/-- Every element of a cyclic fourth nilpotent product is the image of a
canonical Hall product in the free class-three truncation. -/
theorem mapped_standard_hall
    {t : ℕ} (order : Fin t → ℕ)
    (x : NilpotentCyclicProduct order 4) :
    ∃ e : StandardExponentFamily.{u} t,
      inverseTruncation.{u} order
          (standardHallProduct t 4 e) =
        x := by
  obtain ⟨y, rfl⟩ :=
    free_truncation_surjective.{u} order x
  obtain ⟨e, he, _⟩ :=
    unique_hall_coordinates t 4 y
  exact ⟨e, congrArg (inverseTruncation.{u} order) he⟩

/-- The recursive order attached to one canonical Hall factor. -/
noncomputable def standardFactorOrder
    {t r : ℕ} (order : Fin t → ℕ)
    (i : (standardHallFamily.{u} t r).index) : ℕ :=
  hallTreeOrder (fun j : FreeGenerator.{u} t => order j.down)
    (concreteBasicTree i)

/-- Every canonical Hall factor has positive recursive order when all
generator orders are positive. -/
theorem standard_order_pos
    {t r : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, 0 < order i)
    (i : (standardHallFamily.{u} t r).index) :
    0 < standardFactorOrder order i := by
  exact tree_order_pos
    (fun j : FreeGenerator.{u} t => order j.down)
    (fun j => horder j.down)
    (concreteBasicTree i)

/-- A canonical Hall factor, evaluated in the cyclic nilpotent product
through the inverse-generator map, has order dividing its recursive leaf
gcd. -/
theorem mapped_standard_order
    {t r : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (i : (standardHallFamily.{u} t r).index) :
    inverseTruncation.{u} order
          ((standardHallFamily.{u} t r).commutator i
            |>.freeLowerTruncation (n := 4)) ^
        standardFactorOrder order i =
      1 := by
  let value : FreeGenerator.{u} t →
      NilpotentCyclicProduct order 4 :=
    fun j => (nilpotentCyclicGenerator order 4 j.down)⁻¹
  have hvalue :
      ∀ j, value j ^ order j.down = 1 := by
    intro j
    simpa [value] using congrArg Inv.inv
      (nilpotent_cyclic_generator
        order 4 j.down)
  have htree :=
    tree_order_three
      (nilpotent_four_bot order)
      (fun j : FreeGenerator.{u} t => order j.down)
      (fun j => horder j.down)
      value hvalue
      (concreteBasicTree i)
  simpa [standardFactorOrder, value,
    BCWt.freeLowerTruncation,
    freeTruncationValue,
    concrete_basic_word,
    inverseTruncation, CWord.map_eval] using htree

end P1960
end Struik
