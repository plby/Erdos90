import Submission.Group.HilbertJenningsFox
import Submission.Group.ProPPresentation
import Submission.Group.Words
import Submission.Algebra.Linear.FiniteRankMaps
import Submission.Algebra.DenseGenerators.DimensionSubgroup
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Data.Finsupp.Fintype

/-!
# Finite truncation relation modules for completed Fox estimates

The completed Fox inequality for a free pro-`p` presentation has two logically
separate parts.

* The continuous relation-module theorem says that closed normal generation by
  relators covers the generator-boundary kernel after passing to a fixed finite
  augmentation truncation.
* Finite-dimensional linear algebra turns that fixed-degree coverage into the
  required numerical inequality.

This file formalizes the second part and gives a precise interface for the
first.  In particular, the datum below is fixed-degree and topology-free after
construction: it does not mention augmentation-layer prefix ranks or the final
Vinberg recurrence.
-/

open scoped BigOperators Pointwise Topology

noncomputable section

namespace Submission
namespace ProP

open TBluepr

universe u v

/-- The finite quotient group algebra used by the completed Fox truncations. -/
abbrev completedFoxAlgebra
    (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q] : Type u :=
  MonoidAlgebra (ZMod p) Q

/-- The augmentation ideal in the finite quotient group algebra. -/
abbrev completedFoxIdeal
    (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q] :
    Ideal (completedFoxAlgebra p Q) :=
  GroupAlgebra.augmentationIdeal (ZMod p) Q

/-- The quotient group algebra modulo the `n`th augmentation power. -/
abbrev completedFoxTruncation
    (p : ℕ) [Fact p.Prime] (Q : Type u) [Group Q] (n : ℕ) : Type u :=
  GroupAlgebra.augmentationTruncation (ZMod p) Q n

/-- Coordinatewise augmentation-power conditions on a finite tuple. -/
def completedFoxSubmodule
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {ι : Type v} [Fintype ι]
    (degree : ι → ℕ) :
    Submodule (ZMod p) (ι → completedFoxAlgebra p Q) :=
  Submodule.pi Set.univ (fun i =>
    ((completedFoxIdeal p Q) ^ degree i).restrictScalars
      (ZMod p))

@[simp]
theorem completed_fox_submodule
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {ι : Type v} [Fintype ι]
    (degree : ι → ℕ)
    (x : ι → completedFoxAlgebra p Q) :
    x ∈ completedFoxSubmodule (p := p) (Q := Q) degree ↔
      ∀ i, x i ∈ (completedFoxIdeal p Q) ^ degree i := by
  simp [completedFoxSubmodule]

/-- Coordinatewise truncation of a finite coefficient tuple. -/
abbrev completedTupleTruncation
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {ι : Type v} [Fintype ι]
    (degree : ι → ℕ) : Type max u v :=
  (ι → completedFoxAlgebra p Q) ⧸
    completedFoxSubmodule (p := p) (Q := Q) degree

/-- A tuple quotient is the product of its coordinate truncations. -/
noncomputable def completedFoxTuple
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {ι : Type v} [Fintype ι]
    (degree : ι → ℕ) :
    completedTupleTruncation (p := p) (Q := Q) degree ≃ₗ[ZMod p]
      (∀ i : ι, completedFoxTruncation p Q (degree i)) := by
  classical
  simpa only [completedTupleTruncation,
    completedFoxSubmodule,
    completedFoxTruncation,
    GroupAlgebra.augmentationTruncation,
    GroupAlgebra.augmentationPower] using
      (Submodule.quotientPi
        (fun i : ι =>
          ((completedFoxIdeal p Q) ^ degree i).restrictScalars
            (ZMod p)))

/-- Coordinate tuple quotients are finite-dimensional for finite quotient groups. -/
theorem module_tuple_truncation
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {ι : Type v} [Fintype ι]
    (degree : ι → ℕ) :
    Module.Finite (ZMod p)
      (completedTupleTruncation (p := p) (Q := Q) degree) := by
  letI : Fintype Q := Fintype.ofFinite Q
  letI : ∀ i : ι, Module.Finite (ZMod p)
      (completedFoxTruncation p Q (degree i)) :=
    fun _ => by infer_instance
  letI : ∀ i : ι, Module.Free (ZMod p)
      (completedFoxTruncation p Q (degree i)) :=
    fun _ => Module.Free.of_divisionRing _ _
  exact Module.Finite.equiv
    (completedFoxTuple
      (p := p) (Q := Q) degree).symm

/-- Dimension of a finite coordinate tuple quotient. -/
theorem fox_tuple_truncation
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {ι : Type v} [Fintype ι]
    (degree : ι → ℕ) :
    Module.finrank (ZMod p)
        (completedTupleTruncation (p := p) (Q := Q) degree) =
      ∑ i, Module.finrank (ZMod p)
        (completedFoxTruncation p Q (degree i)) := by
  letI : Fintype Q := Fintype.ofFinite Q
  letI : ∀ i : ι, Module.Finite (ZMod p)
      (completedFoxTruncation p Q (degree i)) :=
    fun _ => by infer_instance
  letI : ∀ i : ι, Module.Free (ZMod p)
      (completedFoxTruncation p Q (degree i)) :=
    fun _ => Module.Free.of_divisionRing _ _
  rw [(completedFoxTuple
    (p := p) (Q := Q) degree).finrank_eq]
  exact Module.finrank_pi_fintype (ZMod p)

/-- The image in the finite quotient algebra of one free pro-`p` generator difference. -/
def completedFoxDifference
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (i : Fin d) :
    completedFoxAlgebra p Q :=
  MonoidAlgebra.of (ZMod p) Q (quotientMap (F.generator i)) - 1

/-- Every quotient generator difference belongs to the augmentation ideal. -/
theorem completed_fox_difference
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (i : Fin d) :
    completedFoxDifference F quotientMap i ∈
      completedFoxIdeal p Q := by
  change
    MonoidAlgebra.of (ZMod p) Q (quotientMap (F.generator i)) - 1 ∈
      GroupAlgebra.augmentationIdeal (ZMod p) Q
  rw [GroupAlgebra.mem_augmentationIdeal]
  simp

/-- Right multiplication boundary for the displayed pro-`p` generators. -/
noncomputable def completedFoxBoundary
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q) :
    (Fin d → completedFoxAlgebra p Q) →ₗ[ZMod p]
      completedFoxAlgebra p Q where
  toFun x :=
    ∑ i, x i * completedFoxDifference F quotientMap i
  map_add' x y := by
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp [Pi.smul_apply, Finset.smul_sum]

/-- Boundary multiplication raises the coordinatewise augmentation filtration by one. -/
theorem completed_fox_boundary
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (n : ℕ)
    (x : Fin d → completedFoxAlgebra p Q)
    (hx : x ∈ completedFoxSubmodule
      (p := p) (Q := Q) (fun _ : Fin d => n)) :
    completedFoxBoundary F quotientMap x ∈
      ((completedFoxIdeal p Q) ^ (n + 1)).restrictScalars
        (ZMod p) := by
  classical
  let I : Ideal (completedFoxAlgebra p Q) :=
    completedFoxIdeal p Q
  haveI : I.IsTwoSided := by
    dsimp [I, completedFoxIdeal, GroupAlgebra.augmentationIdeal]
    infer_instance
  change
    ∑ i, x i * completedFoxDifference F quotientMap i ∈ I ^ (n + 1)
  apply Ideal.sum_mem
  intro i _hi
  have hxi : x i ∈ I ^ n := by
    simpa [I] using
      (completed_fox_submodule
        (p := p) (Q := Q) (fun _ : Fin d => n) x).mp hx i
  have hgen :
      completedFoxDifference F quotientMap i ∈ I ^ 1 := by
    simpa [I, Submodule.pow_one] using
      completed_fox_difference F quotientMap i
  have hmul :
      x i * completedFoxDifference F quotientMap i ∈
        I ^ n * I ^ 1 :=
    Ideal.mul_mem_mul hxi hgen
  rw [Ideal.IsTwoSided.pow_add (I := I) (m := n) (n := 1)]
  simpa using hmul

/-- The quotient-level generator boundary in one fixed augmentation degree. -/
noncomputable def completedBoundaryTruncation
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (n : ℕ) :
    completedTupleTruncation
        (p := p) (Q := Q) (fun _ : Fin d => n) →ₗ[ZMod p]
      completedFoxTruncation p Q (n + 1) := by
  let SM :=
    completedFoxSubmodule
      (p := p) (Q := Q) (fun _ : Fin d => n)
  let SN : Submodule (ZMod p) (completedFoxAlgebra p Q) :=
    ((completedFoxIdeal p Q) ^ (n + 1)).restrictScalars
      (ZMod p)
  let μ := completedFoxBoundary F quotientMap
  have hSM : SM ≤ SN.comap μ := by
    intro x hx
    exact completed_fox_boundary
      F quotientMap n x hx
  simpa only [completedTupleTruncation,
    completedFoxTruncation,
    GroupAlgebra.augmentationTruncation,
    GroupAlgebra.augmentationPower, SM, SN, μ] using
      SM.mapQ SN μ hSM

/--
A fixed-degree continuous Fox relation-module datum.

The datum does not assert the Vinberg inequality.  It records only the
finite-truncation relation map and the exact kernel coverage needed by the
linear-algebra argument.
-/
structure CFDatum
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    {ι : Type v} [Fintype ι]
    (_relator : ι → F.Carrier)
    (depth : ι → ℕ)
    (n : ℕ) where
  relatorToGenerator :
    completedTupleTruncation
        (p := p) (Q := Q) (fun r : ι => n + 1 - depth r) →ₗ[ZMod p]
      completedTupleTruncation
        (p := p) (Q := Q) (fun _ : Fin d => n)
  coversKernel :
    LinearMap.ker (completedBoundaryTruncation F quotientMap n) ≤
      LinearMap.range relatorToGenerator

namespace CFDatum

/-- A truncation datum gives pointwise relation-tuple lifts of boundary-kernel classes. -/
theorem pointwise_lifts
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q]
    {F : FreeGroup.{u} p d}
    {quotientMap : F.Carrier →* Q}
    {ι : Type v} [Fintype ι]
    {relator : ι → F.Carrier}
    {depth : ι → ℕ}
    {n : ℕ}
    (D : CFDatum
      F quotientMap relator depth n) :
    ∀ x : LinearMap.ker
        (completedBoundaryTruncation F quotientMap n),
      ∃ y : completedTupleTruncation
          (p := p) (Q := Q) (fun r : ι => n + 1 - depth r),
        D.relatorToGenerator y =
          (x : completedTupleTruncation
            (p := p) (Q := Q) (fun _ : Fin d => n)) := by
  intro x
  have hx :
      (x : completedTupleTruncation
        (p := p) (Q := Q) (fun _ : Fin d => n)) ∈
          LinearMap.range D.relatorToGenerator :=
    D.coversKernel x.2
  exact hx

/-- A truncation datum bounds the dimension of the generator-boundary kernel. -/
theorem kernel_finrank_le
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {F : FreeGroup.{u} p d}
    {quotientMap : F.Carrier →* Q}
    {ι : Type v} [Fintype ι]
    {relator : ι → F.Carrier}
    {depth : ι → ℕ}
    {n : ℕ}
    (D : CFDatum
      F quotientMap relator depth n) :
    Module.finrank (ZMod p)
        (LinearMap.ker
          (completedBoundaryTruncation F quotientMap n)) ≤
      Module.finrank (ZMod p)
        (completedTupleTruncation
          (p := p) (Q := Q) (fun r : ι => n + 1 - depth r)) := by
  letI : Module.Finite (ZMod p)
      (completedTupleTruncation
        (p := p) (Q := Q) (fun r : ι => n + 1 - depth r)) :=
    module_tuple_truncation
      (p := p) (Q := Q) (fun r : ι => n + 1 - depth r)
  exact linear_finrank_range
    (completedBoundaryTruncation F quotientMap n)
    D.relatorToGenerator
    D.coversKernel

end CFDatum

/--
The finite tuple images of the free pro-`p` generators generate whenever the
kernel is closed.

This is a topology-only bridge: it contains no group-algebra truncations and
no Fox derivatives.  The proof uses the finite union of kernel cosets in the
pullback of the abstract generator subgroup.
-/
theorem generator_top_closed
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (_quotientMap_continuous : Continuous quotientMap)
    (_quotientMap_surjective : Function.Surjective quotientMap)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier)) :
    Subgroup.closure (Set.range fun i => quotientMap (F.generator i)) = ⊤ := by
  let K : Subgroup F.Carrier := MonoidHom.ker quotientMap
  letI : K.FiniteIndex := by
    dsimp [K]
    infer_instance
  have hKopen : IsOpen ((K : Subgroup F.Carrier) : Set F.Carrier) :=
    K.isOpen_of_isClosed_of_finiteIndex (by simpa [K] using _closedKernel)
  let H : Subgroup Q :=
    Subgroup.closure (Set.range fun i => quotientMap (F.generator i))
  have hK_le : K ≤ H.comap quotientMap := by
    intro x hx
    change quotientMap x ∈ H
    have hx' : quotientMap x = 1 := by
      simpa [K] using hx
    rw [hx']
    exact H.one_mem
  have hpreopen : IsOpen (((H.comap quotientMap : Subgroup F.Carrier) : Set F.Carrier)) :=
    Subgroup.isOpen_mono hK_le hKopen
  have hpreclosed :
      IsClosed (((H.comap quotientMap : Subgroup F.Carrier) : Set F.Carrier)) :=
    (H.comap quotientMap).isClosed_of_isOpen hpreopen
  have hgen_le :
      Subgroup.closure (Set.range F.generator) ≤ H.comap quotientMap := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hdense_le :
      Subgroup.topologicalClosure (Subgroup.closure (Set.range F.generator)) ≤
        H.comap quotientMap :=
    pro_topological_closed hgen_le hpreclosed
  have htop_pre : (⊤ : Subgroup F.Carrier) ≤ H.comap quotientMap := by
    intro x _hx
    apply hdense_le
    rw [F.dense_generator]
    trivial
  apply top_unique
  intro y _hy
  rcases _quotientMap_surjective y with ⟨x, rfl⟩
  exact htop_pre trivial

lemma tmp_monoid_discrete
    {Γ Λ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [Group Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (φ : Γ →* Λ)
    (hker : IsOpen ((φ.ker : Subgroup Γ) : Set Γ)) :
    Continuous (fun x : Γ => φ x) := by
  classical
  have hsingle :
      ∀ y : Λ, IsOpen ((fun x : Γ => φ x) ⁻¹' ({y} : Set Λ)) := by
    intro y
    by_cases hy : ∃ a : Γ, φ a = y
    · rcases hy with ⟨a, ha⟩
      have hfiber_eq :
          ((fun x : Γ => φ x) ⁻¹' ({y} : Set Λ)) =
            (fun x : Γ => a⁻¹ * x) ⁻¹' (((φ.ker : Subgroup Γ) : Set Γ)) := by
        ext x
        constructor
        · intro hx
          change φ x = y at hx
          change φ (a⁻¹ * x) = 1
          calc
            φ (a⁻¹ * x) = (φ a)⁻¹ * φ x := by simp
            _ = y⁻¹ * y := by rw [ha, hx]
            _ = 1 := by simp
        · intro hx
          change φ (a⁻¹ * x) = 1 at hx
          have hmul : y⁻¹ * φ x = 1 := by
            calc
              y⁻¹ * φ x = (φ a)⁻¹ * φ x := by rw [ha]
              _ = φ (a⁻¹ * x) := by simp
              _ = 1 := hx
          exact (inv_mul_eq_one.mp hmul).symm
      have hshift : Continuous (fun x : Γ => a⁻¹ * x) := by
        continuity
      simpa [hfiber_eq] using hker.preimage hshift
    · have hfiber_empty :
          ((fun x : Γ => φ x) ⁻¹' ({y} : Set Λ)) = ∅ := by
        ext x
        constructor
        · intro hx
          change φ x = y at hx
          exact False.elim (hy ⟨x, hx⟩)
        · intro hx
          exact False.elim hx
      simp [hfiber_empty]
  rw [continuous_def]
  intro U _hU
  have hpre_eq :
      ((fun x : Γ => φ x) ⁻¹' U) =
        ⋃ y : U, ((fun x : Γ => φ x) ⁻¹' ({(y : Λ)} : Set Λ)) := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.2
        ⟨⟨φ x, hx⟩, by simp⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨y, hy⟩
      change φ x ∈ U
      change φ x = y at hy
      exact hy.symm ▸ y.2
  rw [hpre_eq]
  exact isOpen_iUnion fun y => hsingle y

noncomputable def tmp_fox_prod
    {p : ℕ} [Fact p.Prime]
    (Q : Type u) [Group Q] :
    Submission.Theorems.FoxPair (ZMod p) Q ≃
      MonoidAlgebra (ZMod p) Q × Q where
  toFun x := (x.deriv, x.elt)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tmp_fox_pair
    {p : ℕ} [Fact p.Prime]
    (Q : Type u) [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) :
    IsPGroup p (Submission.Theorems.FoxPair (ZMod p) Q) := by
  classical
  letI : DecidableEq Q := Classical.decEq Q
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype (MonoidAlgebra (ZMod p) Q) :=
    show Fintype (Q →₀ ZMod p) from inferInstance
  letI : Finite (Submission.Theorems.FoxPair (ZMod p) Q) :=
    Finite.of_equiv (MonoidAlgebra (ZMod p) Q × Q)
      (tmp_fox_prod Q).symm
  rcases IsPGroup.exists_card_eq hQ with ⟨m, hm⟩
  apply IsPGroup.of_card (n := Fintype.card Q + m)
  rw [Nat.card_congr (tmp_fox_prod Q)]
  rw [Nat.card_eq_fintype_card, Fintype.card_prod]
  change Fintype.card (Q →₀ ZMod p) * Fintype.card Q =
    p ^ (Fintype.card Q + m)
  rw [Fintype.card_finsupp, ZMod.card, ← Nat.card_eq_fintype_card, hm, pow_add]

theorem tmp_discrete_pro
    {p : ℕ} [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Finite G]
    (hG : IsPGroup p G) :
    ProPGroup p G := by
  intro N
  exact hG.to_quotient (N : Subgroup G)

theorem tmp_p_group
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (_quotientMap_surjective : Function.Surjective quotientMap)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier)) :
    IsPGroup p Q := by
  let K : Subgroup F.Carrier := MonoidHom.ker quotientMap
  letI : K.FiniteIndex := by
    dsimp [K]
    infer_instance
  have hKopen : IsOpen ((K : Subgroup F.Carrier) : Set F.Carrier) :=
    K.isOpen_of_isClosed_of_finiteIndex (by simpa [K] using _closedKernel)
  let N : OpenNormalSubgroup F.Carrier :=
    { toOpenSubgroup := ⟨K, hKopen⟩
      isNormal' := by
        dsimp [K]
        infer_instance }
  exact
    (F.isProP N).of_equiv
      (QuotientGroup.quotientKerEquivOfSurjective quotientMap
        _quotientMap_surjective)

noncomputable def tmp_completed_aux
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (j : Fin d) :
    F.Carrier →* Submission.Theorems.FoxPair (ZMod p) Q := by
  letI : DecidableEq Q := Classical.decEq Q
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype (MonoidAlgebra (ZMod p) Q) :=
    show Fintype (Q →₀ ZMod p) from inferInstance
  let P := Submission.Theorems.FoxPair (ZMod p) Q
  letI : Finite P :=
    Finite.of_equiv (MonoidAlgebra (ZMod p) Q × Q)
      (tmp_fox_prod Q).symm
  letI : TopologicalSpace P := ⊥
  letI : DiscreteTopology P := ⟨rfl⟩
  letI : IsTopologicalGroup P := by infer_instance
  letI : CompactSpace P := Finite.compactSpace
  letI : TotallyDisconnectedSpace P := by infer_instance
  exact
    (F.lift
      (tmp_discrete_pro P (tmp_fox_pair Q hQ))
      (fun i =>
        { deriv := if i = j then 1 else 0
          elt := quotientMap (F.generator i) })).toMonoidHom

@[simp]
theorem tmp_fox_aux
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (j i : Fin d) :
    tmp_completed_aux F quotientMap hQ j (F.generator i) =
      { deriv := if i = j then 1 else 0
        elt := quotientMap (F.generator i) } := by
  simp [tmp_completed_aux, F.lift_generator]

theorem tmp_aux_elt
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    (j : Fin d)
    (x : F.Carrier) :
    (tmp_completed_aux F quotientMap hQ j x).elt = quotientMap x := by
  classical
  letI : DecidableEq Q := Classical.decEq Q
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype (MonoidAlgebra (ZMod p) Q) :=
    show Fintype (Q →₀ ZMod p) from inferInstance
  let P := Submission.Theorems.FoxPair (ZMod p) Q
  letI : Finite P :=
    Finite.of_equiv (MonoidAlgebra (ZMod p) Q × Q)
      (tmp_fox_prod Q).symm
  letI : TopologicalSpace P := ⊥
  letI : DiscreteTopology P := ⟨rfl⟩
  letI : IsTopologicalGroup P := by infer_instance
  letI : CompactSpace P := Finite.compactSpace
  letI : TotallyDisconnectedSpace P := by infer_instance
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := ⟨rfl⟩
  letI : IsTopologicalGroup Q := by infer_instance
  letI : T2Space Q := by infer_instance
  let gen : Fin d → P := fun i =>
    { deriv := if i = j then 1 else 0
      elt := quotientMap (F.generator i) }
  let hP : ProPGroup p P :=
    tmp_discrete_pro P (tmp_fox_pair Q hQ)
  let f : ContinuousHom F.Carrier Q :=
    { toMonoidHom :=
        (Submission.Theorems.FoxPair.eltHom (R := ZMod p) (G := Q)).comp
          (F.lift hP gen).toMonoidHom
      continuous_toFun :=
        (show Continuous
            (fun z : P =>
              Submission.Theorems.FoxPair.eltHom (R := ZMod p) (G := Q) z) from
          continuous_of_discreteTopology).comp
            (F.lift hP gen).continuous_toFun }
  let K : Subgroup F.Carrier := MonoidHom.ker quotientMap
  letI : K.FiniteIndex := by
    dsimp [K]
    infer_instance
  have hKopen : IsOpen ((K : Subgroup F.Carrier) : Set F.Carrier) :=
    K.isOpen_of_isClosed_of_finiteIndex (by simpa [K] using _closedKernel)
  let g : ContinuousHom F.Carrier Q :=
    { toMonoidHom := quotientMap
      continuous_toFun :=
        tmp_monoid_discrete quotientMap
          (by simpa [K] using hKopen) }
  have hfg : f = g := by
    apply FGBuild.ContinuousHom.ext_topologi_generates
      F.dense_generator
    intro i
    change (F.lift hP gen (F.generator i)).elt =
      quotientMap (F.generator i)
    rw [F.lift_generator]
  have hx := congrArg (fun h : ContinuousHom F.Carrier Q => h x) hfg
  simpa [tmp_completed_aux, f, g, gen, hP] using hx

noncomputable def completed_fox_derivative
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (j : Fin d)
    (x : F.Carrier) :
    completedFoxAlgebra p Q :=
  (tmp_completed_aux F quotientMap hQ j x).deriv

@[simp]
theorem tmp_derivative_one
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (j : Fin d) :
    completed_fox_derivative F quotientMap hQ j 1 = 0 := by
  simp [completed_fox_derivative]

theorem tmp_completed_mul
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    (j : Fin d)
    (x y : F.Carrier) :
    completed_fox_derivative F quotientMap hQ j (x * y) =
      completed_fox_derivative F quotientMap hQ j x +
        MonoidAlgebra.single (quotientMap x) 1 *
          completed_fox_derivative F quotientMap hQ j y := by
  simp [completed_fox_derivative,
    tmp_aux_elt F quotientMap hQ _closedKernel j x]

@[simp]
theorem tmp_derivative_generator
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (j i : Fin d) :
    completed_fox_derivative F quotientMap hQ j (F.generator i) =
      if i = j then 1 else 0 := by
  simp [completed_fox_derivative]

noncomputable def tmp_deriv_linear
    {p : ℕ} [Fact p.Prime]
    (Q : Type u) [Group Q] :
    MonoidAlgebra (ZMod p) (Submission.Theorems.FoxPair (ZMod p) Q) →ₗ[ZMod p]
      MonoidAlgebra (ZMod p) Q :=
  Finsupp.linearCombination (ZMod p) fun x => x.deriv

@[simp]
theorem tmp_deriv_single
    {p : ℕ} [Fact p.Prime]
    (Q : Type u) [Group Q]
    (x : Submission.Theorems.FoxPair (ZMod p) Q)
    (a : ZMod p) :
    tmp_deriv_linear Q (Finsupp.single x a) = a • x.deriv := by
  exact Finsupp.linearCombination_single (ZMod p) a x

theorem tmp_pair_deriv
    {p : ℕ} [Fact p.Prime]
    (Q : Type u) [Group Q]
    (x y : MonoidAlgebra (ZMod p) (Submission.Theorems.FoxPair (ZMod p) Q)) :
    tmp_deriv_linear Q (x * y) =
      GroupAlgebra.augmentation (ZMod p)
          (Submission.Theorems.FoxPair (ZMod p) Q) y •
        tmp_deriv_linear Q x +
      GroupAlgebra.mapGroupHom (ZMod p)
          (Submission.Theorems.FoxPair.eltHom (R := ZMod p) (G := Q)) x *
        tmp_deriv_linear Q y := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      simp
  | add x z hx hz =>
      simp [add_mul, hx, hz]
      abel
  | single a r =>
      induction y using MonoidAlgebra.induction_linear with
      | zero =>
          simp
      | add y z hy hz =>
          simp [mul_add, hy, hz]
          module
      | single b s =>
          rw [MonoidAlgebra.single_mul_single]
          simp only [tmp_deriv_single,
            GroupAlgebra.augmentation_single, GroupAlgebra.group_hom_single]
          change
            (r * s) • (a * b).deriv =
              s • (r • a.deriv) +
                MonoidAlgebra.single a.elt r * (s • b.deriv)
          rw [Submission.Theorems.FoxPair.deriv_mul]
          ext q
          simp [MonoidAlgebra.single_mul_apply]
          ring

theorem tmp_deriv_pred
    {p : ℕ} [Fact p.Prime]
    (Q : Type u) [Group Q]
    {n : ℕ}
    {x : MonoidAlgebra (ZMod p) (Submission.Theorems.FoxPair (ZMod p) Q)}
    (hx :
      x ∈
        (GroupAlgebra.augmentationIdeal
          (ZMod p) (Submission.Theorems.FoxPair (ZMod p) Q)) ^ n) :
    tmp_deriv_linear Q x ∈
      (GroupAlgebra.augmentationIdeal (ZMod p) Q) ^ (n - 1) := by
  classical
  let IP : Ideal
      (MonoidAlgebra (ZMod p) (Submission.Theorems.FoxPair (ZMod p) Q)) :=
    GroupAlgebra.augmentationIdeal
      (ZMod p) (Submission.Theorems.FoxPair (ZMod p) Q)
  let IQ : Ideal (MonoidAlgebra (ZMod p) Q) :=
    GroupAlgebra.augmentationIdeal (ZMod p) Q
  cases n with
  | zero =>
      simp [Submodule.pow_zero]
  | succ n =>
      have hxmul : x ∈ IP ^ n * IP := by
        simpa [IP, Submodule.pow_succ] using hx
      have htarget : tmp_deriv_linear Q x ∈ IQ ^ n := by
        refine Submodule.mul_induction_on hxmul ?_ ?_
        · intro a ha b hb
          rw [tmp_pair_deriv]
          have haug :
              GroupAlgebra.augmentation (ZMod p)
                (Submission.Theorems.FoxPair (ZMod p) Q) b = 0 := by
            exact
              (GroupAlgebra.mem_augmentationIdeal
                (R := ZMod p)
                (G := Submission.Theorems.FoxPair (ZMod p) Q)).mp
                (by simpa [IP] using hb)
          rw [haug, zero_smul, zero_add]
          have hmap :
              GroupAlgebra.mapGroupHom (ZMod p)
                  (Submission.Theorems.FoxPair.eltHom (R := ZMod p) (G := Q)) a ∈
                IQ ^ n := by
            simpa [IQ, IP] using
              GroupAlgebra.group_augmentation_power
                (ZMod p)
                (Submission.Theorems.FoxPair.eltHom (R := ZMod p) (G := Q))
                (by simpa [IP] using ha)
          exact (IQ ^ n).mul_mem_right _ hmap
        · intro a b ha hb
          rw [map_add]
          exact (IQ ^ n).add_mem ha hb
      simpa [IQ] using htarget

@[simp]
theorem tmp_fox_deriv
    {p : ℕ} [Fact p.Prime]
    (Q : Type u) [Group Q]
    (x : Submission.Theorems.FoxPair (ZMod p) Q) :
    tmp_deriv_linear Q
        (MonoidAlgebra.of (ZMod p)
          (Submission.Theorems.FoxPair (ZMod p) Q) x - 1) =
      x.deriv := by
  change
    tmp_deriv_linear Q
        (Finsupp.single x 1 - Finsupp.single (1 :
          Submission.Theorems.FoxPair (ZMod p) Q) 1) =
      x.deriv
  calc
    tmp_deriv_linear Q
          (Finsupp.single x 1 - Finsupp.single (1 :
            Submission.Theorems.FoxPair (ZMod p) Q) 1) =
        tmp_deriv_linear Q (Finsupp.single x 1) -
          tmp_deriv_linear Q
            (Finsupp.single (1 : Submission.Theorems.FoxPair (ZMod p) Q) 1) := by
      exact map_sub (tmp_deriv_linear Q) _ _
    _ = x.deriv := by
      rw [tmp_deriv_single,
        tmp_deriv_single]
      simp

theorem tmp_derivative_pred
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (j : Fin d)
    {depth : ℕ}
    {x : F.Carrier}
    (hx :
      x ∈
        (zassenhausFiltration p F.Carrier depth).topologicalClosure) :
    completed_fox_derivative F quotientMap hQ j x ∈
      (completedFoxIdeal p Q) ^ (depth - 1) := by
  classical
  letI : DecidableEq Q := Classical.decEq Q
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype (MonoidAlgebra (ZMod p) Q) :=
    show Fintype (Q →₀ ZMod p) from inferInstance
  let P := Submission.Theorems.FoxPair (ZMod p) Q
  letI : Finite P :=
    Finite.of_equiv (MonoidAlgebra (ZMod p) Q × Q)
      (tmp_fox_prod Q).symm
  letI : TopologicalSpace P := ⊥
  letI : DiscreteTopology P := ⟨rfl⟩
  letI : IsTopologicalGroup P := by infer_instance
  letI : CompactSpace P := Finite.compactSpace
  letI : TotallyDisconnectedSpace P := by infer_instance
  let gen : Fin d → P := fun i =>
    { deriv := if i = j then 1 else 0
      elt := quotientMap (F.generator i) }
  let hP : ProPGroup p P :=
    tmp_discrete_pro P (tmp_fox_pair Q hQ)
  let aux : F.Carrier →* P := tmp_completed_aux F quotientMap hQ j
  have haux_cont : Continuous (fun z : F.Carrier => aux z) := by
    simpa [aux, tmp_completed_aux, gen, hP] using
      (F.lift hP gen).continuous_toFun
  have hle :
      zassenhausFiltration p F.Carrier depth ≤
        (zassenhausFiltration p P depth).comap aux := by
    intro z hz
    exact filtration_map_mem p depth aux hz
  have hpreclosed :
      IsClosed
        ((((zassenhausFiltration p P depth).comap aux : Subgroup F.Carrier) :
          Set F.Carrier)) := by
    change
      IsClosed
        ((fun z : F.Carrier => aux z) ⁻¹'
          ((zassenhausFiltration p P depth : Subgroup P) : Set P))
    exact (isClosed_discrete _).preimage haux_cont
  have hxaux : aux x ∈ zassenhausFiltration p P depth := by
    exact
      (pro_topological_closed hle hpreclosed) hx
  have hsub :
      MonoidAlgebra.of (ZMod p) P (aux x) - 1 ∈
        (GroupAlgebra.augmentationIdeal (ZMod p) P) ^ depth := by
    simpa [TBluepr.golod_shafarevich_algebra] using
      (GShafar.zassenhaus_filtration_subgroup
        (p := p) (G := P) depth hxaux)
  have hderiv :=
    tmp_deriv_pred Q hsub
  rw [tmp_fox_deriv] at hderiv
  simpa [aux, completed_fox_derivative] using hderiv

theorem tmp_completed_inv
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    (j : Fin d)
    (x : F.Carrier) :
    completed_fox_derivative F quotientMap hQ j x⁻¹ =
      -(MonoidAlgebra.single (quotientMap x⁻¹) 1 *
        completed_fox_derivative F quotientMap hQ j x) := by
  change
    (tmp_completed_aux F quotientMap hQ j x⁻¹).deriv =
      -(MonoidAlgebra.single (quotientMap x⁻¹) 1 *
        (tmp_completed_aux F quotientMap hQ j x).deriv)
  rw [map_inv]
  change
    -(MonoidAlgebra.single
        ((tmp_completed_aux F quotientMap hQ j x).elt⁻¹) 1 *
      (tmp_completed_aux F quotientMap hQ j x).deriv) =
      -(MonoidAlgebra.single (quotientMap x⁻¹) 1 *
        (tmp_completed_aux F quotientMap hQ j x).deriv)
  rw [tmp_aux_elt F quotientMap hQ _closedKernel]
  simp

noncomputable def completed_derivative_tuple
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (x : F.Carrier) :
    Fin d → completedFoxAlgebra p Q :=
  fun j => completed_fox_derivative F quotientMap hQ j x

theorem tmp_derivative_mul
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    (x y : F.Carrier) :
    completed_derivative_tuple F quotientMap hQ (x * y) =
      fun j =>
        completed_derivative_tuple F quotientMap hQ x j +
          MonoidAlgebra.single (quotientMap x) 1 *
            completed_derivative_tuple F quotientMap hQ y j := by
  funext j
  exact
    tmp_completed_mul F quotientMap hQ _closedKernel j x y

theorem tmp_derivative_inv
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    (x : F.Carrier) :
    completed_derivative_tuple F quotientMap hQ x⁻¹ =
      fun j =>
        -(MonoidAlgebra.single (quotientMap x⁻¹) 1 *
          completed_derivative_tuple F quotientMap hQ x j) := by
  funext j
  exact tmp_completed_inv F quotientMap hQ _closedKernel j x

noncomputable def tmp_fox_relator
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    {ι : Type v} [Fintype ι]
    (relator : ι → F.Carrier) :
    (ι → completedFoxAlgebra p Q) →ₗ[ZMod p]
      (Fin d → completedFoxAlgebra p Q) where
  toFun c j :=
    ∑ r, c r * completed_derivative_tuple F quotientMap hQ (relator r) j
  map_add' x y := by
    ext j
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    ext j
    simp [Pi.smul_apply, Finset.smul_sum]

theorem tmp_completed_range
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    {ι : Type v} [Fintype ι]
    (relator : ι → F.Carrier)
    (a : completedFoxAlgebra p Q)
    {x : Fin d → completedFoxAlgebra p Q}
    (hx : x ∈ LinearMap.range
      (tmp_fox_relator F quotientMap hQ relator)) :
    (fun j => a * x j) ∈ LinearMap.range
      (tmp_fox_relator F quotientMap hQ relator) := by
  classical
  rcases hx with ⟨c, rfl⟩
  refine ⟨fun r => a * c r, ?_⟩
  ext j
  simp [tmp_fox_relator, mul_assoc, Finset.mul_sum]

theorem tmp_fox_derivative
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    {ι : Type v} [Fintype ι]
    (relator : ι → F.Carrier)
    (_kernel_eq :
      MonoidHom.ker quotientMap =
        (Subgroup.normalClosure (Set.range relator)).topologicalClosure)
    {x : F.Carrier}
    (hx : x ∈ MonoidHom.ker quotientMap) :
    completed_derivative_tuple F quotientMap hQ x ∈
      LinearMap.range
        (tmp_fox_relator F quotientMap hQ relator) := by
  classical
  let A := completedFoxAlgebra p Q
  let rangeS : Submodule (ZMod p) (Fin d → A) :=
    LinearMap.range (tmp_fox_relator F quotientMap hQ relator)
  let N : Subgroup F.Carrier :=
    { carrier := {z | quotientMap z = 1 ∧
          completed_derivative_tuple F quotientMap hQ z ∈ rangeS}
      one_mem' := by
        constructor
        · simp
        · refine ⟨0, ?_⟩
          funext j
          simp [tmp_fox_relator, completed_derivative_tuple]
      mul_mem' := by
        intro a b ha hb
        constructor
        · simp [ha.1, hb.1]
        · rw [tmp_derivative_mul
            F quotientMap hQ _closedKernel]
          refine rangeS.add_mem ha.2 ?_
          exact
            tmp_completed_range
              F quotientMap hQ relator
              (MonoidAlgebra.single (quotientMap a) 1) hb.2
      inv_mem' := by
        intro a ha
        constructor
        · simp [ha.1]
        · rw [tmp_derivative_inv
            F quotientMap hQ _closedKernel]
          have hmul :
              (fun j =>
                MonoidAlgebra.single (quotientMap a⁻¹) 1 *
                  completed_derivative_tuple F quotientMap hQ a j) ∈
                rangeS :=
            tmp_completed_range
              F quotientMap hQ relator
              (MonoidAlgebra.single (quotientMap a⁻¹) 1) ha.2
          simpa [Pi.neg_apply] using rangeS.neg_mem hmul }
  have hNnormal : N.Normal := by
    refine Subgroup.Normal.mk ?_
    intro z hz a
    constructor
    · simp [hz.1]
    · have htuple :
          completed_derivative_tuple F quotientMap hQ (a * z * a⁻¹) =
            fun j =>
              MonoidAlgebra.single (quotientMap a) 1 *
                completed_derivative_tuple F quotientMap hQ z j := by
        ext j
        rw [tmp_derivative_mul
          F quotientMap hQ _closedKernel]
        rw [tmp_derivative_mul
          F quotientMap hQ _closedKernel]
        rw [tmp_derivative_inv
          F quotientMap hQ _closedKernel]
        simp [hz.1]
      rw [htuple]
      exact
        tmp_completed_range
          F quotientMap hQ relator
          (MonoidAlgebra.single (quotientMap a) 1) hz.2
  have hrels_le : Set.range relator ⊆ (N : Set F.Carrier) := by
    rintro _ ⟨i, rfl⟩
    constructor
    · have hi :
          relator i ∈
            (Subgroup.normalClosure (Set.range relator)).topologicalClosure :=
        (Subgroup.normalClosure (Set.range relator)).le_topologicalClosure
          (Subgroup.subset_normalClosure ⟨i, rfl⟩)
      simpa [← _kernel_eq, MonoidHom.mem_ker] using hi
    · refine ⟨fun k => if k = i then 1 else 0, ?_⟩
      ext j
      simp [tmp_fox_relator]
  have hnormal_le : Subgroup.normalClosure (Set.range relator) ≤ N := by
    letI : N.Normal := hNnormal
    exact Subgroup.normalClosure_le_normal hrels_le
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  have htuple_cont :
      Continuous
        (fun z : F.Carrier =>
          completed_derivative_tuple F quotientMap hQ z) := by
    apply continuous_pi
    intro j
    letI : DecidableEq Q := Classical.decEq Q
    letI : Fintype Q := Fintype.ofFinite Q
    letI : Fintype (MonoidAlgebra (ZMod p) Q) :=
      show Fintype (Q →₀ ZMod p) from inferInstance
    let P := Submission.Theorems.FoxPair (ZMod p) Q
    letI : Finite P :=
      Finite.of_equiv (MonoidAlgebra (ZMod p) Q × Q)
        (tmp_fox_prod Q).symm
    letI : TopologicalSpace P := ⊥
    letI : DiscreteTopology P := ⟨rfl⟩
    letI : IsTopologicalGroup P := by infer_instance
    letI : CompactSpace P := Finite.compactSpace
    letI : TotallyDisconnectedSpace P := by infer_instance
    let gen : Fin d → P := fun i =>
      { deriv := if i = j then 1 else 0
        elt := quotientMap (F.generator i) }
    let hP : ProPGroup p P :=
      tmp_discrete_pro P (tmp_fox_pair Q hQ)
    have hproj : Continuous (fun z : P => z.deriv) :=
      continuous_of_discreteTopology
    simpa [completed_derivative_tuple, completed_fox_derivative,
      tmp_completed_aux, gen, hP] using
        hproj.comp (F.lift hP gen).continuous_toFun
  have hNclosed : IsClosed ((N : Subgroup F.Carrier) : Set F.Carrier) := by
    change
      IsClosed
        ((MonoidHom.ker quotientMap : Set F.Carrier) ∩
          (fun z : F.Carrier =>
            completed_derivative_tuple F quotientMap hQ z) ⁻¹'
              (rangeS : Set (Fin d → A)))
    have hrange_pre :
        IsClosed
          ((fun z : F.Carrier =>
            completed_derivative_tuple F quotientMap hQ z) ⁻¹'
              (rangeS : Set (Fin d → A))) :=
      (isClosed_discrete (rangeS : Set (Fin d → A))).preimage htuple_cont
    exact _closedKernel.inter hrange_pre
  have htop_le :
      (Subgroup.normalClosure (Set.range relator)).topologicalClosure ≤ N :=
    pro_topological_closed hnormal_le hNclosed
  exact (htop_le (_kernel_eq ▸ hx)).2

noncomputable def tmp_freeEval
    {p d : ℕ} [Fact p.Prime]
    (F : FreeGroup.{u} p d) :
    _root_.FreeGroup (Fin d) →* F.Carrier :=
  _root_.FreeGroup.lift F.generator

@[simp]
theorem tmp_free_generator
    {p d : ℕ} [Fact p.Prime]
    (F : FreeGroup.{u} p d)
    (i : Fin d) :
    tmp_freeEval F (_root_.FreeGroup.of i) = F.generator i := by
  simp [tmp_freeEval]

noncomputable def tmp_fox_tuple
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q) :
    MonoidAlgebra (ZMod p) (_root_.FreeGroup (Fin d)) →ₗ[ZMod p]
      (Fin d → completedFoxAlgebra p Q) :=
  Finsupp.linearCombination (ZMod p) fun w =>
    completed_derivative_tuple F quotientMap hQ (tmp_freeEval F w)

@[simp]
theorem tmp_derivative_single
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (w : _root_.FreeGroup (Fin d))
    (a : ZMod p) :
    tmp_fox_tuple F quotientMap hQ
        (Finsupp.single w a) =
      a • completed_derivative_tuple F quotientMap hQ (tmp_freeEval F w) := by
  exact Finsupp.linearCombination_single (ZMod p) a w

theorem tmp_completed_fox
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    (x y : MonoidAlgebra (ZMod p) (_root_.FreeGroup (Fin d))) :
    tmp_fox_tuple F quotientMap hQ (x * y) =
      GroupAlgebra.augmentation (ZMod p) (_root_.FreeGroup (Fin d)) y •
        tmp_fox_tuple F quotientMap hQ x +
      fun j =>
        GroupAlgebra.mapGroupHom (ZMod p) (quotientMap.comp (tmp_freeEval F)) x *
          tmp_fox_tuple F quotientMap hQ y j := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero =>
      funext j
      simp
  | add x z hx hz =>
      funext j
      simp [add_mul, hx, hz, Pi.add_apply]
      abel
  | single a r =>
      induction y using MonoidAlgebra.induction_linear with
      | zero =>
          funext j
          simp
      | add y z hy hz =>
          funext j
          simp [mul_add, hy, hz, Pi.add_apply]
          module
      | single b s =>
          rw [MonoidAlgebra.single_mul_single]
          simp only [tmp_derivative_single,
            GroupAlgebra.augmentation_single, GroupAlgebra.group_hom_single,
            map_mul]
          rw [tmp_derivative_mul
            F quotientMap hQ _closedKernel]
          funext j
          ext q
          simp [MonoidAlgebra.single_mul_apply]
          ring

@[simp]
theorem tmp_completed_derivative
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (w : _root_.FreeGroup (Fin d)) :
    tmp_fox_tuple F quotientMap hQ
        (MonoidAlgebra.of (ZMod p) (_root_.FreeGroup (Fin d)) w - 1) =
      completed_derivative_tuple F quotientMap hQ (tmp_freeEval F w) := by
  change
    tmp_fox_tuple F quotientMap hQ
        (Finsupp.single w 1 -
          Finsupp.single (1 : _root_.FreeGroup (Fin d)) 1) =
      completed_derivative_tuple F quotientMap hQ (tmp_freeEval F w)
  calc
    tmp_fox_tuple F quotientMap hQ
          (Finsupp.single w 1 -
            Finsupp.single (1 : _root_.FreeGroup (Fin d)) 1) =
        tmp_fox_tuple F quotientMap hQ
            (Finsupp.single w 1) -
          tmp_fox_tuple F quotientMap hQ
            (Finsupp.single (1 : _root_.FreeGroup (Fin d)) 1) := by
      exact map_sub (tmp_fox_tuple F quotientMap hQ) _ _
    _ = completed_derivative_tuple F quotientMap hQ (tmp_freeEval F w) := by
      rw [tmp_derivative_single,
        tmp_derivative_single]
      funext j
      simp [completed_derivative_tuple]

@[simp]
theorem tmp_free_derivative
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q) :
    tmp_fox_tuple F quotientMap hQ 1 = 0 := by
  change
    tmp_fox_tuple F quotientMap hQ
        (Finsupp.single (1 : _root_.FreeGroup (Fin d)) 1) =
      0
  rw [tmp_derivative_single]
  funext j
  simp [completed_derivative_tuple]

theorem tmp_derivative_tuple
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    (a : MonoidAlgebra (ZMod p) (_root_.FreeGroup (Fin d)))
    (w : _root_.FreeGroup (Fin d)) :
    tmp_fox_tuple F quotientMap hQ
        (a * (MonoidAlgebra.of (ZMod p) (_root_.FreeGroup (Fin d)) w - 1)) =
      fun j =>
        GroupAlgebra.mapGroupHom (ZMod p) (quotientMap.comp (tmp_freeEval F)) a *
          completed_derivative_tuple F quotientMap hQ (tmp_freeEval F w) j := by
  rw [tmp_completed_fox
    F quotientMap hQ _closedKernel]
  simp

theorem tmp_boundary_range
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (_quotientMap_continuous : Continuous quotientMap)
    (_quotientMap_surjective : Function.Surjective quotientMap)
    {ι : Type v} [Fintype ι]
    (relator : ι → F.Carrier)
    (_kernel_eq :
      MonoidHom.ker quotientMap =
        (Subgroup.normalClosure (Set.range relator)).topologicalClosure) :
    LinearMap.ker (completedFoxBoundary F quotientMap) ≤
      LinearMap.range
        (tmp_fox_relator F quotientMap
          (tmp_p_group F quotientMap _quotientMap_surjective
            (by
              rw [_kernel_eq]
              exact Subgroup.isClosed_topologicalClosure _))
          relator) := by
  classical
  let A := completedFoxAlgebra p Q
  let eval : _root_.FreeGroup (Fin d) →* F.Carrier := tmp_freeEval F
  let q0 : _root_.FreeGroup (Fin d) →* Q :=
    _root_.FreeGroup.lift fun i => quotientMap (F.generator i)
  have hq0_eval : q0 = quotientMap.comp eval := by
    ext i
    simp [q0, eval]
  have hclosedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier) := by
    rw [_kernel_eq]
    exact Subgroup.isClosed_topologicalClosure _
  let hQ : IsPGroup p Q :=
    tmp_p_group F quotientMap _quotientMap_surjective hclosedKernel
  let qmap :
      MonoidAlgebra (ZMod p) (_root_.FreeGroup (Fin d)) →ₐ[ZMod p] A :=
    GroupAlgebra.mapGroupHom (ZMod p) q0
  let L :
      MonoidAlgebra (ZMod p) (_root_.FreeGroup (Fin d)) →ₗ[ZMod p]
        (Fin d → A) :=
    tmp_fox_tuple F quotientMap hQ
  let rangeS : Submodule (ZMod p) (Fin d → A) :=
    LinearMap.range (tmp_fox_relator F quotientMap hQ relator)
  have hq0_surj : Function.Surjective q0 := by
    rw [← MonoidHom.range_eq_top]
    dsimp [q0]
    rw [_root_.FreeGroup.range_lift_eq_closure]
    exact
      generator_top_closed
        F quotientMap _quotientMap_continuous _quotientMap_surjective
          hclosedKernel
  have hrel_le :
      GroupAlgebra.kRIdeal (R := ZMod p) q0 ≤
        { carrier := {z | qmap z = 0 ∧ L z ∈ rangeS}
          zero_mem' := by simp
          add_mem' := by
            intro x y hx hy
            constructor
            · simp [hx.1, hy.1]
            · simpa using rangeS.add_mem hx.2 hy.2
          smul_mem' := by
            intro a z hz
            constructor
            · simp [hz.1]
            · have haug :
                  GroupAlgebra.augmentation
                    (ZMod p) (_root_.FreeGroup (Fin d)) z = 0 := by
                rw [← GroupAlgebra.augmentation_group_hom (ZMod p) q0 z]
                rw [show GroupAlgebra.mapGroupHom (ZMod p) q0 z = 0 by
                  exact hz.1]
                simp
              have hL :
                  L (a * z) =
                    fun j => qmap a * L z j := by
                rw [show L =
                    tmp_fox_tuple
                      F quotientMap hQ from rfl]
                rw [tmp_completed_fox
                  F quotientMap hQ hclosedKernel]
                rw [haug, zero_smul, zero_add]
                simp [qmap, hq0_eval, eval]
              change L (a * z) ∈ rangeS
              rw [hL]
              exact
                tmp_completed_range
                  F quotientMap hQ relator (qmap a) hz.2 } := by
    apply Ideal.span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    constructor
    · change
        GroupAlgebra.mapGroupHom (ZMod p) q0
            (MonoidAlgebra.of (ZMod p) (_root_.FreeGroup (Fin d)) k - 1) =
          0
      rw [map_sub, map_one]
      simp only [MonoidAlgebra.of_apply, GroupAlgebra.group_hom_single]
      rw [MonoidHom.mem_ker.mp hk]
      rw [← MonoidAlgebra.one_def, sub_self]
    · rw [show L =
          tmp_fox_tuple F quotientMap hQ from rfl]
      rw [tmp_completed_derivative]
      apply
        tmp_fox_derivative
          F quotientMap hQ hclosedKernel relator _kernel_eq
      change quotientMap (eval k) = 1
      have hk' : q0 k = 1 := MonoidHom.mem_ker.mp hk
      simpa [hq0_eval] using hk'
  intro y hy
  have hqmap_surj : Function.Surjective qmap := by
    simpa [qmap, GroupAlgebra.mapGroupHom] using
      GroupAlgebra.domain_hom_surjective (R := ZMod p) q0 hq0_surj
  choose Y hY using fun j : Fin d => hqmap_surj (y j)
  let B : MonoidAlgebra (ZMod p) (_root_.FreeGroup (Fin d)) :=
    ∑ j, Y j *
      (MonoidAlgebra.of (ZMod p) (_root_.FreeGroup (Fin d))
        (_root_.FreeGroup.of j) - 1)
  have hqB : qmap B = 0 := by
    have hqB_boundary :
        qmap B = completedFoxBoundary F quotientMap y := by
      dsimp [B]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [map_mul, hY j]
      rw [show qmap = GroupAlgebra.mapGroupHom (ZMod p) q0 from rfl]
      rw [map_sub, map_one]
      rw [GroupAlgebra.group_hom_single]
      simp [q0, completedFoxDifference, MonoidAlgebra.of_apply]
    rw [hqB_boundary]
    exact LinearMap.mem_ker.mp hy
  have hBrel :
      B ∈ GroupAlgebra.kRIdeal (R := ZMod p) q0 := by
    rw [← GroupAlgebra.domain_relation_surjective
      (R := ZMod p) q0 hq0_surj]
    exact hqB
  have hBJ := hrel_le hBrel
  have hLB : L B = y := by
    funext j
    dsimp [B]
    rw [map_sum]
    simp only [Finset.sum_apply]
    have hmapY (i : Fin d) :
        GroupAlgebra.mapGroupHom
            (ZMod p) (quotientMap.comp (tmp_freeEval F)) (Y i) =
          y i := by
      rw [← hq0_eval]
      exact hY i
    calc
      ∑ i, L (Y i *
          (MonoidAlgebra.single (_root_.FreeGroup.of i) 1 - 1)) j =
          ∑ i, y i * (if i = j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _hi
        change
          L (Y i *
              (MonoidAlgebra.of (ZMod p) (_root_.FreeGroup (Fin d))
                (_root_.FreeGroup.of i) - 1)) j =
            y i * (if i = j then 1 else 0)
        rw [show L =
          tmp_fox_tuple F quotientMap hQ from rfl]
        rw [tmp_derivative_tuple
          F quotientMap hQ hclosedKernel]
        rw [hmapY i]
        simp [completed_derivative_tuple]
      _ = y j := by simp
  simpa [rangeS, hLB] using hBJ.2

theorem tmp_boundary_strict
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (_quotientMap_continuous : Continuous quotientMap)
    (_quotientMap_surjective : Function.Surjective quotientMap)
    (_closedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier))
    (n : ℕ)
    (x : Fin d → completedFoxAlgebra p Q)
    (hx :
      completedFoxBoundary F quotientMap x ∈
        ((completedFoxIdeal p Q) ^ (n + 1)).restrictScalars
          (ZMod p)) :
    ∃ y ∈ completedFoxSubmodule
        (p := p) (Q := Q) (fun _ : Fin d => n),
      completedFoxBoundary F quotientMap y =
        completedFoxBoundary F quotientMap x := by
  classical
  let b : GroupAlgebra.augmentationPowerSubmodule (ZMod p) Q (n + 1) :=
    ⟨completedFoxBoundary F quotientMap x, hx⟩
  rcases
      GroupAlgebra.generated_single_top
        (ZMod p) Q (fun i : Fin d => quotientMap (F.generator i))
        (generator_top_closed
          F quotientMap _quotientMap_continuous _quotientMap_surjective
            _closedKernel)
        (n + 1) (by omega) b with
    ⟨y, hy⟩
  refine ⟨fun j => (y j : completedFoxAlgebra p Q), ?_, ?_⟩
  · rw [completed_fox_submodule]
    intro j
    exact (y j).2
  · simpa [b, completedFoxBoundary,
      completedFoxDifference, MonoidAlgebra.of_apply] using hy.symm

theorem tmp_completed_tuple
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (hQ : IsPGroup p Q)
    {ι : Type v} [Fintype ι]
    (relator : ι → F.Carrier)
    (depth : ι → ℕ)
    (_relator_depth :
      ∀ r, relator r ∈
        (zassenhausFiltration p F.Carrier (depth r)).topologicalClosure)
    (n : ℕ)
    (x : ι → completedFoxAlgebra p Q)
    (hx : x ∈ completedFoxSubmodule
      (p := p) (Q := Q) (fun r : ι => n + 1 - depth r)) :
    tmp_fox_relator F quotientMap hQ relator x ∈
      completedFoxSubmodule
        (p := p) (Q := Q) (fun _ : Fin d => n) := by
  classical
  let I : Ideal (completedFoxAlgebra p Q) :=
    completedFoxIdeal p Q
  haveI : I.IsTwoSided := by
    dsimp [I, completedFoxIdeal, GroupAlgebra.augmentationIdeal]
    infer_instance
  rw [completed_fox_submodule]
  intro j
  change
    ∑ r, x r * completed_derivative_tuple
      F quotientMap hQ (relator r) j ∈ I ^ n
  apply Ideal.sum_mem
  intro r _hr
  have hxr : x r ∈ I ^ (n + 1 - depth r) := by
    simpa [I] using
      (completed_fox_submodule
        (p := p) (Q := Q) (fun r : ι => n + 1 - depth r) x).mp hx r
  have hcoeff :
      completed_derivative_tuple F quotientMap hQ (relator r) j ∈
        I ^ (depth r - 1) := by
    change
      completed_fox_derivative F quotientMap hQ j (relator r) ∈
        (completedFoxIdeal p Q) ^ (depth r - 1)
    exact
      tmp_derivative_pred
        F quotientMap hQ j (_relator_depth r)
  have hmul :
      x r * completed_derivative_tuple F quotientMap hQ (relator r) j ∈
        I ^ (n + 1 - depth r) * I ^ (depth r - 1) :=
    Ideal.mul_mem_mul hxr hcoeff
  have hdegree :
      n ≤ (n + 1 - depth r) + (depth r - 1) := by
    omega
  have hle :
      I ^ ((n + 1 - depth r) + (depth r - 1)) ≤ I ^ n :=
    Ideal.pow_le_pow_right hdegree
  apply hle
  rw [Ideal.IsTwoSided.pow_add]
  exact hmul


/--
Closed normal generation supplies a fixed-degree continuous Fox
relation-module datum.

This is the substantive completed-Fox leaf.  It is strictly narrower than the
final inequality: it treats one degree, constructs a relation map between
finite tuple truncations, and proves kernel coverage.  It contains no
augmentation-layer prefix sums and no numerical rank comparison.
-/
theorem nonempty_datum_generation
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [Finite Q]
    (F : FreeGroup.{u} p d)
    (quotientMap : F.Carrier →* Q)
    (_quotientMap_continuous : Continuous quotientMap)
    (_quotientMap_surjective : Function.Surjective quotientMap)
    {ι : Type v} [Fintype ι]
    (relator : ι → F.Carrier)
    (_kernel_eq :
      MonoidHom.ker quotientMap =
        (Subgroup.normalClosure (Set.range relator)).topologicalClosure)
    (depth : ι → ℕ)
    (_relator_depth :
      ∀ r, relator r ∈
        (zassenhausFiltration p F.Carrier (depth r)).topologicalClosure)
    (n : ℕ) :
    Nonempty
      (CFDatum
        F quotientMap relator depth n) := by
  classical
  have hclosedKernel :
      IsClosed ((MonoidHom.ker quotientMap : Subgroup F.Carrier) : Set F.Carrier) := by
    rw [_kernel_eq]
    exact Subgroup.isClosed_topologicalClosure _
  let hQ : IsPGroup p Q :=
    tmp_p_group
      F quotientMap _quotientMap_surjective hclosedKernel
  let A := completedFoxAlgebra p Q
  let SR : Submodule (ZMod p) (ι → A) :=
    completedFoxSubmodule
      (p := p) (Q := Q) (fun r : ι => n + 1 - depth r)
  let SM : Submodule (ZMod p) (Fin d → A) :=
    completedFoxSubmodule
      (p := p) (Q := Q) (fun _ : Fin d => n)
  let SN : Submodule (ZMod p) A :=
    ((completedFoxIdeal p Q) ^ (n + 1)).restrictScalars
      (ZMod p)
  let φ : (ι → A) →ₗ[ZMod p] (Fin d → A) :=
    tmp_fox_relator F quotientMap hQ relator
  let μ : (Fin d → A) →ₗ[ZMod p] A :=
    completedFoxBoundary F quotientMap
  have hSR : SR ≤ SM.comap φ := by
    intro x hx
    exact
      tmp_completed_tuple
        F quotientMap hQ relator depth _relator_depth n x hx
  have hSM : SM ≤ SN.comap μ := by
    intro x hx
    exact
      completed_fox_boundary
        F quotientMap n x hx
  have hexact : LinearMap.ker μ ≤ LinearMap.range φ := by
    dsimp [μ, φ]
    exact
      tmp_boundary_range
        F quotientMap _quotientMap_continuous _quotientMap_surjective
          relator _kernel_eq
  have hstrict : ∀ m, μ m ∈ SN → ∃ s ∈ SM, μ s = μ m := by
    intro m hm
    exact
      tmp_boundary_strict
        F quotientMap _quotientMap_continuous _quotientMap_surjective
          hclosedKernel n m hm
  let φq := SR.mapQ SM φ hSR
  let μq := SM.mapQ SN μ hSM
  have hcover : LinearMap.ker μq ≤ LinearMap.range φq := by
    exact
      range_exact_strict
        φ μ SR SM SN hSR hSM hexact hstrict
  refine ⟨{ relatorToGenerator := ?_, coversKernel := ?_ }⟩
  · simpa only [completedTupleTruncation, SR, SM, φ] using φq
  · simpa only [completedBoundaryTruncation,
      completedTupleTruncation, completedFoxTruncation,
      GroupAlgebra.augmentationTruncation, GroupAlgebra.augmentationPower,
      SR, SM, SN, φ, μ, φq, μq] using hcover

/-- The fixed-degree relation datum gives the unguarded truncation-rank estimate. -/
theorem completed_truncation_relator
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {F : FreeGroup.{u} p d}
    {quotientMap : F.Carrier →* Q}
    {ι : Type v} [Fintype ι]
    {relator : ι → F.Carrier}
    {depth : ι → ℕ}
    {n : ℕ}
    (D : CFDatum
      F quotientMap relator depth n) :
    d * Module.finrank (ZMod p)
        (completedFoxTruncation p Q n) ≤
      Module.finrank (ZMod p)
          (completedFoxTruncation p Q (n + 1)) +
        ∑ r, Module.finrank (ZMod p)
          (completedFoxTruncation p Q (n + 1 - depth r)) := by
  classical
  let μ :=
    completedBoundaryTruncation F quotientMap n
  let R :=
    completedTupleTruncation
      (p := p) (Q := Q) (fun r : ι => n + 1 - depth r)
  let M :=
    completedTupleTruncation
      (p := p) (Q := Q) (fun _ : Fin d => n)
  let N :=
    completedFoxTruncation p Q (n + 1)
  letI : Module.Finite (ZMod p) R := by
    dsimp [R]
    exact module_tuple_truncation
      (p := p) (Q := Q) (fun r : ι => n + 1 - depth r)
  letI : Module.Finite (ZMod p) M := by
    dsimp [M]
    exact module_tuple_truncation
      (p := p) (Q := Q) (fun _ : Fin d => n)
  letI : Module.Finite (ZMod p) N := by
    dsimp [N, completedFoxTruncation]
    infer_instance
  have hker :
      Module.finrank (ZMod p) (LinearMap.ker μ) ≤
        Module.finrank (ZMod p) R := by
    simpa [μ, R] using
      CFDatum.kernel_finrank_le D
  have hrank := rank_nullity μ
  have hrange :
      Module.finrank (ZMod p) (LinearMap.range μ) ≤
        Module.finrank (ZMod p) N :=
    Submodule.finrank_le (LinearMap.range μ)
  have hquot :
      Module.finrank (ZMod p) M ≤
        Module.finrank (ZMod p) N + Module.finrank (ZMod p) R := by
    dsimp [M, N, R, μ] at hker hrank hrange ⊢
    omega
  calc
    d * Module.finrank (ZMod p)
          (completedFoxTruncation p Q n) =
        Module.finrank (ZMod p) M := by
          dsimp [M]
          rw [fox_tuple_truncation]
          simp
    _ ≤ Module.finrank (ZMod p) N + Module.finrank (ZMod p) R := hquot
    _ = Module.finrank (ZMod p)
          (completedFoxTruncation p Q (n + 1)) +
        ∑ r, Module.finrank (ZMod p)
          (completedFoxTruncation p Q (n + 1 - depth r)) := by
          dsimp [N, R]
          rw [fox_tuple_truncation]

/-- Subtraction in the source truncation is the guarded relator contribution. -/
theorem completed_fox_guarded
    {p : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    (n depth : ℕ) :
    Module.finrank (ZMod p)
        (completedFoxTruncation p Q (n + 1 - depth)) =
      if depth ≤ n then
        Module.finrank (ZMod p)
          (completedFoxTruncation p Q (n - depth + 1))
      else 0 := by
  by_cases hdepth : depth ≤ n
  · rw [if_pos hdepth]
    have hdegree : n + 1 - depth = n - depth + 1 := by
      omega
    rw [hdegree]
  · rw [if_neg hdepth]
    have hzero : n + 1 - depth = 0 := by
      omega
    rw [hzero]
    exact GroupAlgebra.augmentation_finrank_zero
      (K := ZMod p) (G := Q)

/-- Guarded-convolution form of the fixed-degree truncation-rank estimate. -/
theorem completed_guarded_relator
    {p d : ℕ} [Fact p.Prime]
    {Q : Type u} [Group Q] [Finite Q]
    {F : FreeGroup.{u} p d}
    {quotientMap : F.Carrier →* Q}
    {ι : Type v} [Fintype ι]
    {relator : ι → F.Carrier}
    {depth : ι → ℕ}
    {n : ℕ}
    (D : CFDatum
      F quotientMap relator depth n) :
    d * Module.finrank (ZMod p)
        (completedFoxTruncation p Q n) ≤
      Module.finrank (ZMod p)
          (completedFoxTruncation p Q (n + 1)) +
        ∑ r,
          if depth r ≤ n then
            Module.finrank (ZMod p)
              (completedFoxTruncation p Q (n - depth r + 1))
          else 0 := by
  simpa only [
    completed_fox_guarded
      (p := p) (Q := Q) n] using
    completed_truncation_relator D

end ProP
end Submission
