import Mathlib.GroupTheory.Congruence.Hom
import Towers.Group.NilpotentProducts.GeneralCardinality


/-!
# Finite specializations for Struik's Theorem 2

An order `0` denotes an infinite cyclic factor.  Replacing every such
order by one positive odd integer gives a finite odd-order problem, and
there are natural specialization maps on both the cyclic nilpotent
product and the equation-(18) coordinate group.
-/

namespace Struik
namespace P1960

open Towers
open Towers.TCTex

/-- Replace every infinite cyclic factor by a cyclic factor of order
`M`, leaving finite factors unchanged. -/
def oddSpecializationOrder
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) (i : Fin t) : ℕ :=
  if order i = 0 then M else order i

@[simp] theorem finite_odd_specialization
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) (i : Fin t)
    (hi : order i = 0) :
    oddSpecializationOrder order M i = M := by
  simp [oddSpecializationOrder, hi]

@[simp] theorem odd_specialization_ne
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) (i : Fin t)
    (hi : order i ≠ 0) :
    oddSpecializationOrder order M i = order i := by
  simp [oddSpecializationOrder, hi]

/-- Every specialized order divides the corresponding original order;
for an original order `0`, this is the convention that every natural
number divides zero. -/
theorem odd_specialization_dvd
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) (i : Fin t) :
    oddSpecializationOrder order M i ∣ order i := by
  by_cases hi : order i = 0
  · simp [oddSpecializationOrder, hi]
  · simp [oddSpecializationOrder, hi]

/-- Specializing admissible orders at an odd integer produces odd
positive orders. -/
theorem odd_specialization_order
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M) (i : Fin t) :
    Odd (oddSpecializationOrder order M i) := by
  rcases horder i with hi | hi
  · simpa [oddSpecializationOrder, hi] using hM
  · have hne : order i ≠ 0 := hi.pos.ne'
    simpa [oddSpecializationOrder, hne] using hi

theorem odd_specialization_admissible
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M) (i : Fin t) :
    AOrd (oddSpecializationOrder order M i) :=
  AOrd.of_odd
    (odd_specialization_order order horder hM i)

/-- Every specialized pair modulus divides the original pair modulus. -/
theorem modulus_specialization_dvd
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ)
    (q : Pair t) :
    generalPairModulus (oddSpecializationOrder order M) q ∣
      generalPairModulus order q := by
  apply Nat.dvd_gcd
  · exact
      (Nat.gcd_dvd_left
        (oddSpecializationOrder order M q.i)
        (oddSpecializationOrder order M q.j)).trans
        (odd_specialization_dvd order M q.i)
  · exact
      (Nat.gcd_dvd_right
        (oddSpecializationOrder order M q.i)
        (oddSpecializationOrder order M q.j)).trans
        (odd_specialization_dvd order M q.j)

/-- Every specialized triple modulus divides the original triple
modulus. -/
theorem triple_modulus_specialization
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ)
    (q : Triple t) :
    generalResiduesModulus
        (oddSpecializationOrder order M) q ∣
      generalResiduesModulus order q := by
  apply Nat.dvd_gcd
  · apply Nat.dvd_gcd
    · exact
        (Nat.gcd_dvd_left
          (Nat.gcd
            (oddSpecializationOrder order M q.i)
            (oddSpecializationOrder order M q.j))
          (oddSpecializationOrder order M q.k)).trans
          ((Nat.gcd_dvd_left
            (oddSpecializationOrder order M q.i)
            (oddSpecializationOrder order M q.j)).trans
            (odd_specialization_dvd order M q.i))
    · exact
        (Nat.gcd_dvd_left
          (Nat.gcd
            (oddSpecializationOrder order M q.i)
            (oddSpecializationOrder order M q.j))
          (oddSpecializationOrder order M q.k)).trans
          ((Nat.gcd_dvd_right
            (oddSpecializationOrder order M q.i)
            (oddSpecializationOrder order M q.j)).trans
            (odd_specialization_dvd order M q.j))
  · exact
      (Nat.gcd_dvd_right
        (Nat.gcd
          (oddSpecializationOrder order M q.i)
          (oddSpecializationOrder order M q.j))
        (oddSpecializationOrder order M q.k)).trans
        (odd_specialization_dvd order M q.k)

/-- Coordinate congruence for the original orders implies coordinate
congruence after finite specialization. -/
theorem GMEq.specialize
    {t : ℕ} {order : Fin t → ℕ} {M : ℕ}
    {c d : GCoordi t}
    (h : GMEq order c d) :
    GMEq
      (oddSpecializationOrder order M) c d :=
  ⟨fun i => mod_dvd_nat (h.single i)
      (odd_specialization_dvd order M i),
    fun q => mod_dvd_nat (h.pair q)
      (modulus_specialization_dvd order M q),
    fun q => mod_dvd_nat (h.pairLeft q)
      (modulus_specialization_dvd order M q),
    fun q => mod_dvd_nat (h.pairRight q)
      (modulus_specialization_dvd order M q),
    fun q => mod_dvd_nat (h.tripleFirst q)
      (triple_modulus_specialization order M q),
    fun q => mod_dvd_nat (h.tripleSecond q)
      (triple_modulus_specialization order M q)⟩

/-- The natural map from the original equation-(18) residue group to a
finite specialization. -/
noncomputable def generalResidueSpecialization
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M) :
    GeneralResidueGroup order horder →*
      GeneralResidueGroup
        (oddSpecializationOrder order M)
        (odd_specialization_admissible order horder hM) :=
  Con.map
    (generalCon order horder)
    (generalCon
      (oddSpecializationOrder order M)
      (odd_specialization_admissible order horder hM))
    fun _ _ h => h.specialize

@[simp] theorem general_specialization_coe
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M)
    (c : GCoordi t) :
    generalResidueSpecialization order horder hM
        (c : GeneralResidueGroup order horder) =
      (c : GeneralResidueGroup
        (oddSpecializationOrder order M)
        (odd_specialization_admissible order horder hM)) :=
  rfl

@[simp] theorem general_specialization_generator
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M) (i : Fin t) :
    generalResidueSpecialization order horder hM
        (generalResidueGenerator order horder i) =
      generalResidueGenerator
        (oddSpecializationOrder order M)
        (odd_specialization_admissible order horder hM) i := by
  rfl

/-- The natural map between the free products induced by finite
specialization. -/
noncomputable def cyclicFreeSpecialization
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) :
    CyclicFreeProduct order →*
      CyclicFreeProduct (oddSpecializationOrder order M) := by
  refine PresentedGroup.toGroup
    (f := cyclicGenerator (oddSpecializationOrder order M)) ?_
  intro r hr
  obtain ⟨i, rfl⟩ := hr
  by_cases hi : order i = 0
  · simp [hi]
  · simpa [oddSpecializationOrder, hi] using
      cyclic_generator_order
        (oddSpecializationOrder order M) i

@[simp] theorem cyclic_specialization_generator
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) (i : Fin t) :
    cyclicFreeSpecialization order M
        (cyclicGenerator order i) =
      cyclicGenerator (oddSpecializationOrder order M) i := by
  unfold cyclicFreeSpecialization cyclicGenerator
  exact PresentedGroup.toGroup.of _

/-- Finite specialization descends to the fourth nilpotent products. -/
noncomputable def nilpotentFourSpecialization
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) :
    NilpotentCyclicProduct order 4 →*
      NilpotentCyclicProduct
        (oddSpecializationOrder order M) 4 :=
  QuotientGroup.map
    (Subgroup.lowerCentralSeries (CyclicFreeProduct order) 3)
    (Subgroup.lowerCentralSeries
      (CyclicFreeProduct (oddSpecializationOrder order M)) 3)
    (cyclicFreeSpecialization order M)
    (by
      intro x hx
      exact
        Subgroup.lowerCentralSeries.map
          (cyclicFreeSpecialization order M) 3
          (Subgroup.mem_map_of_mem
            (cyclicFreeSpecialization order M) hx))

@[simp] theorem nilpotent_specialization_generator
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) (i : Fin t) :
    nilpotentFourSpecialization order M
        (nilpotentCyclicGenerator order 4 i) =
      nilpotentCyclicGenerator
        (oddSpecializationOrder order M) 4 i := by
  rw [nilpotentFourSpecialization,
    nilpotentCyclicGenerator, QuotientGroup.map_mk']
  rfl

/-- The inverse-generator free truncation map is natural under finite
specialization. -/
theorem inverse_truncation_specialization
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) :
    (nilpotentFourSpecialization order M).comp
        (inverseTruncation.{0} order) =
      inverseTruncation.{0}
        (oddSpecializationOrder order M) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨w, rfl⟩ :=
    QuotientGroup.mk'_surjective
      (Subgroup.lowerCentralSeries
        (FreeGroup (FreeGenerator.{0} t)) 3) x
  let f :
      FreeGroup (FreeGenerator.{0} t) →*
        NilpotentCyclicProduct
          (oddSpecializationOrder order M) 4 :=
    (nilpotentFourSpecialization order M).comp
      (FreeGroup.lift fun i =>
        (nilpotentCyclicGenerator order 4 i.down)⁻¹)
  change
    f w =
      (FreeGroup.lift fun i =>
        (nilpotentCyclicGenerator
          (oddSpecializationOrder order M) 4 i.down)⁻¹) w
  exact FreeGroup.lift_unique f (fun i => by simp [f])

/-- The product of all nonzero generator orders, with every zero order
replaced by the neutral factor `1`. -/
def finiteOrderProduct
    {t : ℕ} (order : Fin t → ℕ) : ℕ :=
  ∏ i, if order i = 0 then 1 else order i

theorem order_product_odd
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Odd (finiteOrderProduct order) := by
  classical
  unfold finiteOrderProduct
  refine Finset.prod_induction
    (s := Finset.univ)
    (f := fun i => if order i = 0 then 1 else order i)
    (p := Odd)
    (fun _ _ ha hb => ha.mul hb) odd_one ?_
  intro i hi
  rcases horder i with hzero | hodd
  · simp [hzero]
  · simp [hodd.pos.ne', hodd]

theorem order_dvd_ne
    {t : ℕ} (order : Fin t → ℕ) (i : Fin t)
    (hi : order i ≠ 0) :
    order i ∣ finiteOrderProduct order := by
  classical
  have hdiv :
      (if order i = 0 then 1 else order i) ∣
        ∏ j, if order j = 0 then 1 else order j :=
    Finset.dvd_prod_of_mem
      (fun j => if order j = 0 then 1 else order j)
      (Finset.mem_univ i)
  simpa [finiteOrderProduct, hi] using hdiv

/-- A specialization modulus large enough to detect a chosen integer
representative while remaining a multiple of every finite generator
order. -/
def hallSeparationModulus
    {t : ℕ} (order : Fin t → ℕ) (e : ℤ) : ℕ :=
  finiteOrderProduct order * (2 * e.natAbs + 1)

theorem separation_modulus_odd
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (e : ℤ) :
    Odd (hallSeparationModulus order e) :=
  (order_product_odd order horder).mul
    ⟨e.natAbs, rfl⟩

theorem separation_modulus_abs
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (e : ℤ) :
    e.natAbs < hallSeparationModulus order e := by
  have hprod : 0 < finiteOrderProduct order :=
    (order_product_odd order horder).pos
  apply Nat.lt_of_lt_of_le (m := 2 * e.natAbs + 1)
  · omega
  · exact Nat.le_mul_of_pos_left (2 * e.natAbs + 1) hprod

theorem or_separation_modulus
    {t : ℕ} (order : Fin t → ℕ) (e : ℤ) (i : Fin t) :
    order i = 0 ∨ order i ∣ hallSeparationModulus order e := by
  by_cases hi : order i = 0
  · exact Or.inl hi
  · exact Or.inr
      (dvd_mul_of_dvd_left
        (order_dvd_ne order i hi)
        (2 * e.natAbs + 1))

/-- A recursive Hall gcd is either zero or divides any common multiple
of all nonzero leaf orders. -/
theorem tree_or_dvd
    {ι : Type*} (order : ι → ℕ) (M : ℕ)
    (horder : ∀ i, order i = 0 ∨ order i ∣ M) :
    ∀ tree : HallTree ι,
      hallTreeOrder order tree = 0 ∨
        hallTreeOrder order tree ∣ M
  | .atom i => horder i
  | .commutator left right => by
      let a := hallTreeOrder order left
      let b := hallTreeOrder order right
      by_cases hgcd : Nat.gcd a b = 0
      · exact Or.inl hgcd
      · right
        rcases tree_or_dvd order M horder left with
          ha | ha
        · rcases tree_or_dvd order M horder right with
            hb | hb
          · exact False.elim (hgcd (by simp [a, b, ha, hb]))
          · simpa [hallTreeOrder, a, b, ha] using hb
        · exact (Nat.gcd_dvd_left a b).trans ha

/-- Under a common finite multiple, specialization preserves every
nonzero recursive Hall gcd and replaces a zero recursive gcd by `M`. -/
theorem tree_order_specialization
    {ι : Type*} (order : ι → ℕ) (M : ℕ)
    (horder : ∀ i, order i = 0 ∨ order i ∣ M) :
    ∀ tree : HallTree ι,
      hallTreeOrder
          (fun i => if order i = 0 then M else order i) tree =
        if hallTreeOrder order tree = 0 then M
        else hallTreeOrder order tree
  | .atom i => by simp [hallTreeOrder]
  | .commutator left right => by
      let a := hallTreeOrder order left
      let b := hallTreeOrder order right
      have ihLeft :=
        tree_order_specialization order M horder left
      have ihRight :=
        tree_order_specialization order M horder right
      have haM :=
        tree_or_dvd order M horder left
      have hbM :=
        tree_or_dvd order M horder right
      by_cases ha : a = 0
      · by_cases hb : b = 0
        · simp [hallTreeOrder, a, b, ha, hb, ihLeft, ihRight]
        · have hbdiv : b ∣ M := hbM.resolve_left hb
          have hgcd : Nat.gcd M b = b :=
            Nat.gcd_eq_right_iff_dvd.mpr hbdiv
          simp [hallTreeOrder, a, b, ha, hb, ihLeft, ihRight, hgcd]
      · by_cases hb : b = 0
        · have hadiv : a ∣ M := haM.resolve_left ha
          have hgcd : Nat.gcd a M = a :=
            Nat.gcd_eq_left_iff_dvd.mpr hadiv
          simp [hallTreeOrder, a, b, ha, hb, ihLeft, ihRight, hgcd]
        · simp [hallTreeOrder, a, b, ha, hb, ihLeft, ihRight]

theorem standard_order_specialization
    {t r : ℕ} (order : Fin t → ℕ) (M : ℕ)
    (horder : ∀ i, order i = 0 ∨ order i ∣ M)
    (i : (standardHallFamily.{0} t r).index) :
    standardFactorOrder
        (oddSpecializationOrder order M) i =
      if standardFactorOrder order i = 0 then M
      else standardFactorOrder order i := by
  unfold standardFactorOrder oddSpecializationOrder
  exact tree_order_specialization
    (fun j : FreeGenerator.{0} t => order j.down) M
    (fun j => horder j.down) (concreteBasicTree i)

/-- Reduce one residue-valued Hall weight block along a finite
specialization. -/
noncomputable def hallResidueSpecialization
    {t : ℕ} (order : Fin t → ℕ) (M r : ℕ)
    (z : ∀ i : (standardHallFamily.{0} t r).index,
      ZMod (standardFactorOrder order i)) :
    ∀ i : (standardHallFamily.{0} t r).index,
      ZMod (standardFactorOrder
        (oddSpecializationOrder order M) i) :=
  fun i => zmodRepresentative (z i)

/-- Reduce one Hall residue tuple along a finite specialization, using
the same chosen integer representatives in every weight. -/
noncomputable def residuesUpSpecialization
    {t : ℕ} (order : Fin t → ℕ) (M : ℕ) :
    ResiduesUpThree.{0} order →
      ResiduesUpThree.{0}
        (oddSpecializationOrder order M)
  | ⟨z₁, z₂, z₃⟩ =>
      ⟨hallResidueSpecialization order M 1 z₁,
        hallResidueSpecialization order M 2 z₂,
        hallResidueSpecialization order M 3 z₃⟩

theorem mapped_general_specialization
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M) (r : ℕ)
    (z : ∀ i : (standardHallFamily.{0} t r).index,
      ZMod (standardFactorOrder order i)) :
    nilpotentFourSpecialization order M
        (mappedGeneralResidue order r z) =
      mappedGeneralResidue
        (oddSpecializationOrder order M) r
        (fun i => (zmodRepresentative (z i) :
          ZMod (standardFactorOrder
            (oddSpecializationOrder order M) i))) := by
  let e : (standardHallFamily.{0} t r).index → ℤ :=
    fun i => zmodRepresentative (z i)
  have hz :
      z = fun i => (e i : ZMod (standardFactorOrder order i)) := by
    funext i
    exact (zmodRepresentative_cast (z i)).symm
  have hsource :
      mappedGeneralResidue order r z =
        inverseTruncation.{0} order
          ((standardHallFamily.{0} t r).collectedWeightProduct
            (n := 4) e) := by
    rw [hz]
    exact mapped_int_cast
      order horder r e
  calc
    nilpotentFourSpecialization order M
        (mappedGeneralResidue order r z) =
        nilpotentFourSpecialization order M
          (inverseTruncation.{0} order
            ((standardHallFamily.{0} t r).collectedWeightProduct
              (n := 4) e)) := congrArg _ hsource
    _ = inverseTruncation.{0}
          (oddSpecializationOrder order M)
          ((standardHallFamily.{0} t r).collectedWeightProduct
            (n := 4) e) :=
      DFunLike.congr_fun
        (inverse_truncation_specialization order M)
        ((standardHallFamily.{0} t r).collectedWeightProduct
          (n := 4) e)
    _ = mappedGeneralResidue
          (oddSpecializationOrder order M) r
          (fun i => (zmodRepresentative (z i) :
            ZMod (standardFactorOrder
              (oddSpecializationOrder order M) i))) := by
      symm
      exact mapped_int_cast
        (oddSpecializationOrder order M)
        (odd_specialization_admissible order horder hM) r e

/-- Evaluating Hall residues commutes with finite specialization. -/
theorem general_residue_specialization
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M)
    (z : ResiduesUpThree.{0} order) :
    nilpotentFourSpecialization order M
        (generalHallResidue order z) =
      generalHallResidue
        (oddSpecializationOrder order M)
        (residuesUpSpecialization order M z) := by
  rcases z with ⟨z₁, z₂, z₃⟩
  simp only [generalHallResidue,
    residuesUpSpecialization, map_mul]
  rw [mapped_general_specialization
      order horder hM 1 z₁,
    mapped_general_specialization
      order horder hM 2 z₂,
    mapped_general_specialization
      order horder hM 3 z₃]
  rfl

@[simp] theorem
    nilpotent_residues_generator
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (i : Fin t) :
    nilpotentGeneralResidues order horder
        (nilpotentCyclicGenerator order 4 i) =
      generalResidueGenerator order horder i := by
  change
    cyclicGeneralResidues order horder
        (cyclicGenerator order i) =
      generalResidueGenerator order horder i
  unfold cyclicGeneralResidues
  exact PresentedGroup.toGroup.of _

/-- The canonical equation-(18) model map commutes with finite
specialization. -/
theorem
    nilpotent_residues_specialization
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M) :
    (generalResidueSpecialization order horder hM).comp
        (nilpotentGeneralResidues
          order horder) =
      (nilpotentGeneralResidues
          (oddSpecializationOrder order M)
          (odd_specialization_admissible
            order horder hM)).comp
        (nilpotentFourSpecialization order M) := by
  apply MonoidHom.eq_of_eqOn_dense
    (range_nilpotent_top order)
  rintro x ⟨i, rfl⟩
  change
    generalResidueSpecialization order horder hM
        (nilpotentGeneralResidues
          order horder
          (nilpotentCyclicGenerator order 4 i)) =
      nilpotentGeneralResidues
        (oddSpecializationOrder order M)
        (odd_specialization_admissible order horder hM)
        (nilpotentFourSpecialization order M
          (nilpotentCyclicGenerator order 4 i))
  rw [nilpotent_residues_generator,
    general_specialization_generator,
    nilpotent_specialization_generator,
    nilpotent_residues_generator]

/-- For finite odd orders, the Hall residue cover is the unique normal
form rather than merely a surjective cover. -/
theorem general_bijective_odd
    {t : ℕ} (order : Fin t → ℕ)
    (hodd : ∀ i, Odd (order i)) :
    Function.Bijective (generalHallResidue.{0} order) := by
  let horder : ∀ i, AOrd (order i) :=
    fun i => AOrd.of_odd (hodd i)
  have horderPos : ∀ i, 0 < order i :=
    fun i => (hodd i).pos
  have hHallSurjective :
      Function.Surjective (generalHallResidue.{0} order) :=
    general_residue_surjective order horder
  letI : Finite (ResiduesUpThree.{0} order) :=
    Nat.finite_of_card_ne_zero
      (residues_up_ne order horderPos)
  letI : Finite (NilpotentCyclicProduct order 4) :=
    Finite.of_surjective
      (generalHallResidue.{0} order) hHallSurjective
  have hcanonical :
      Function.Bijective
        (nilpotentGeneralResidues
          order horder) := by
    simpa [horder] using
      nilpotent_residues_bijective
        order hodd
  have hcard :
      Nat.card (ResiduesUpThree.{0} order) ≤
        Nat.card (NilpotentCyclicProduct order 4) := by
    calc
      Nat.card (ResiduesUpThree.{0} order) =
          Nat.card (GeneralResidueGroup order horder) :=
        residues_up_general
          order horder
      _ = Nat.card (NilpotentCyclicProduct order 4) :=
        (Nat.card_congr
          (Equiv.ofBijective
            (nilpotentGeneralResidues
              order horder)
            hcanonical)).symm
      _ ≤ Nat.card (NilpotentCyclicProduct order 4) := le_rfl
  exact hHallSurjective.bijective_of_nat_card_le hcard

/-- If an element is trivial in the general equation-(18) model, then
it is trivial in every finite odd specialization. -/
theorem nilpotent_specialization_model
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M)
    (x : NilpotentCyclicProduct order 4)
    (hx :
      nilpotentGeneralResidues
          order horder x =
        1) :
    nilpotentFourSpecialization order M x = 1 := by
  let specializedOrder := oddSpecializationOrder order M
  let specializedAdmissible :
      ∀ i, AOrd (specializedOrder i) :=
    odd_specialization_admissible order horder hM
  let specializedModel :=
    nilpotentGeneralResidues
      specializedOrder specializedAdmissible
  have hnatural :=
    DFunLike.congr_fun
      (nilpotent_residues_specialization
        order horder hM) x
  change
    generalResidueSpecialization order horder hM
        (nilpotentGeneralResidues
          order horder x) =
      specializedModel
        (nilpotentFourSpecialization order M x)
    at hnatural
  have hmodel :
      specializedModel
          (nilpotentFourSpecialization order M x) =
        1 := by
    calc
      specializedModel
          (nilpotentFourSpecialization order M x) =
          generalResidueSpecialization order horder hM
            (nilpotentGeneralResidues
              order horder x) := hnatural.symm
      _ = 1 := by rw [hx, map_one]
  have hinjective : Function.Injective specializedModel := by
    exact
      (nilpotent_residues_bijective
        specializedOrder
        (odd_specialization_order order horder hM)).1
  apply hinjective
  rw [map_one]
  exact hmodel

/-- A Hall residue tuple whose evaluation is trivial in the general
model reduces to zero in every finite odd specialization. -/
theorem residues_up_specialization
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    {M : ℕ} (hM : Odd M)
    (z : ResiduesUpThree.{0} order)
    (hz :
      nilpotentGeneralResidues
          order horder (generalHallResidue order z) =
        1) :
    residuesUpSpecialization order M z = 0 := by
  let specializedOrder := oddSpecializationOrder order M
  let specializedAdmissible :
      ∀ i, AOrd (specializedOrder i) :=
    odd_specialization_admissible order horder hM
  have heval :
      generalHallResidue specializedOrder
          (residuesUpSpecialization order M z) =
        1 := by
    rw [← general_residue_specialization
      order horder hM z]
    exact
      nilpotent_specialization_model
        order horder hM (generalHallResidue order z) hz
  have hinjective :
      Function.Injective
        (generalHallResidue.{0} specializedOrder) :=
    (general_bijective_odd specializedOrder
      (odd_specialization_order order horder hM)).1
  apply hinjective
  rw [heval, general_residue_zero
    specializedOrder specializedAdmissible]

/-- If every finite odd reduction of one Hall weight block vanishes,
then the original residue block vanishes. -/
theorem hall_residue_specializations
    {t r : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (z : ∀ i : (standardHallFamily.{0} t r).index,
      ZMod (standardFactorOrder order i))
    (hz :
      ∀ (M : ℕ), Odd M →
        hallResidueSpecialization order M r z = 0) :
    z = 0 := by
  funext i
  let e : ℤ := zmodRepresentative (z i)
  let M : ℕ := hallSeparationModulus order e
  have hM : Odd M := separation_modulus_odd order horder e
  have hcoordinate :=
    congrFun (hz M hM) i
  change
    (e : ZMod (standardFactorOrder
      (oddSpecializationOrder order M) i)) = 0 at hcoordinate
  have hfactor :
      standardFactorOrder
          (oddSpecializationOrder order M) i =
        if standardFactorOrder order i = 0 then M
        else standardFactorOrder order i :=
    standard_order_specialization order M
      (or_separation_modulus order e) i
  by_cases hi : standardFactorOrder order i = 0
  · have hfactorZero :
        standardFactorOrder
            (oddSpecializationOrder order M) i =
          M := by
      simpa [hi] using hfactor
    rw [hfactorZero] at hcoordinate
    have hdiv : (M : ℤ) ∣ e :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd e M).mp hcoordinate
    have he : e = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
      simpa [M, Int.natAbs_natCast] using
        separation_modulus_abs order horder e
    calc
      z i = (e : ZMod (standardFactorOrder order i)) :=
        (zmodRepresentative_cast (z i)).symm
      _ = 0 := by simp [he]
  · have hfactorNonzero :
        standardFactorOrder
            (oddSpecializationOrder order M) i =
          standardFactorOrder order i := by
      simpa [hi] using hfactor
    rw [hfactorNonzero] at hcoordinate
    calc
      z i = (e : ZMod (standardFactorOrder order i)) :=
        (zmodRepresentative_cast (z i)).symm
      _ = 0 := hcoordinate

/-- Finite odd Hall reductions separate the full weight-one through
weight-three residue tuple. -/
theorem residues_up_specializations
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i))
    (z : ResiduesUpThree.{0} order)
    (hz :
      ∀ (M : ℕ), Odd M →
        residuesUpSpecialization order M z = 0) :
    z = 0 := by
  rcases z with ⟨z₁, z₂, z₃⟩
  have hz₁ : z₁ = 0 := by
    apply hall_residue_specializations
      order horder z₁
    intro M hM
    exact congrArg Prod.fst (hz M hM)
  have hz₂ : z₂ = 0 := by
    apply hall_residue_specializations
      order horder z₂
    intro M hM
    exact congrArg (fun x => x.2.1) (hz M hM)
  have hz₃ : z₃ = 0 := by
    apply hall_residue_specializations
      order horder z₃
    intro M hM
    exact congrArg (fun x => x.2.2) (hz M hM)
  simp [hz₁, hz₂, hz₃]

/-- **Struik's Theorem 2, full uniqueness form.**  The canonical
equation-(18) model map is injective when every cyclic order is odd or
zero. -/
theorem
    odd_general_admissible
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Function.Injective
      (nilpotentGeneralResidues
        order horder) := by
  intro x y hxy
  let model :=
    nilpotentGeneralResidues
      order horder
  have hkernel : model (x * y⁻¹) = 1 := by
    simp [model, map_mul, map_inv, hxy]
  obtain ⟨z, hz⟩ :=
    general_residue_surjective order horder (x * y⁻¹)
  have hzmodel :
      model (generalHallResidue order z) = 1 := by
    rw [hz]
    exact hkernel
  have hzspecializes :
      ∀ (M : ℕ), Odd M →
        residuesUpSpecialization order M z = 0 := by
    intro M hM
    exact
      residues_up_specialization
        order horder hM z hzmodel
  have hzzero : z = 0 :=
    residues_up_specializations
      order horder z hzspecializes
  have heval : generalHallResidue order z = 1 := by
    rw [hzzero]
    exact general_residue_zero order horder
  have hmul : x * y⁻¹ = 1 := by
    calc
      x * y⁻¹ = generalHallResidue order z := hz.symm
      _ = 1 := heval
  exact eq_of_mul_inv_eq_one hmul

/-- **Struik's Theorem 2.**  For a finite family of cyclic groups whose
orders are odd or zero, the fourth nilpotent product is canonically
bijective with the equation-(18) residue coordinate group. -/
theorem
    odd_bijective_admissible
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    Function.Bijective
      (nilpotentGeneralResidues
        order horder) :=
  ⟨odd_general_admissible
      order horder,
    nilpotent_general_residues
      order horder⟩

/-- The full odd-or-zero form of Struik's Theorem 2 as an equivalence
with the explicit residue tuple. -/
noncomputable def residue_equiv_admissible
    {t : ℕ} (order : Fin t → ℕ)
    (horder : ∀ i, AOrd (order i)) :
    NilpotentCyclicProduct order 4 ≃
      GeneralResidues order :=
  (Equiv.ofBijective
      (nilpotentGeneralResidues
        order horder)
      (odd_bijective_admissible
        order horder)).trans
    (generalResidueEquiv order horder)

end P1960
end Struik
