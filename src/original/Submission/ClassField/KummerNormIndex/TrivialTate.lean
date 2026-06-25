import Submission.ClassField.HerbrandQuotients.HerbrandIsogeny

/-!
# Trivial cyclic Tate groups for Proposition VII.6.8

This file identifies the universe-polymorphic low Tate groups for a trivial
cyclic action with the cokernel and kernel of multiplication by the order of
the cyclic group.  These are the algebraic groups occurring in Milne's
definition of `h_n(M)`.
-/

namespace Submission.CField.KNIndex

open CategoryTheory CategoryTheory.Limits Representation
open Submission.CField.ICohomo

noncomputable section

universe u v

local instance (priority := 2000) trivialTateCoinvariantsModule
    {G : Type u} [Group G] {A : Type v} [AddCommGroup A] [Module ℤ A]
    (ρ : Representation ℤ G A) : Module ℤ ρ.Coinvariants :=
  Representation.Coinvariants.instModule ρ

local instance (priority := 2000) trivialTateInvariantsModule
    {G : Type u} [Group G] {A : Type v} [AddCommGroup A] [Module ℤ A]
    (ρ : Representation ℤ G A) : Module ℤ ρ.invariants :=
  ρ.invariants.module

/-- The invariants of a trivial representation are its whole carrier. -/
noncomputable def trivialInvariantsEquiv
    (G : Type u) [Group G] (A : Type v) [AddCommGroup A] [Module ℤ A] :
    (Rep.trivial ℤ G A).ρ.invariants ≃+ A where
  toFun x := x.1
  invFun x := ⟨x, by simp [Representation.mem_invariants]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The coinvariants of a trivial representation are its whole carrier. -/
noncomputable def trivialCoinvariantsEquiv
    (G : Type u) [Group G] (A : Type v) [AddCommGroup A] [Module ℤ A] :
    (Rep.trivial ℤ G A).ρ.Coinvariants ≃+ A where
  toFun := Coinvariants.lift (Rep.trivial ℤ G A).ρ LinearMap.id (by simp)
  invFun := Coinvariants.mk (Rep.trivial ℤ G A).ρ
  left_inv x := by
    induction x using Coinvariants.induction_on with
    | _ x => rfl
  right_inv _ := rfl
  map_add' x y := map_add _ x y

@[simp]
theorem trivial_coinvariants_mk
    (G : Type u) [Group G] (A : Type v) [AddCommGroup A] [Module ℤ A]
    (x : A) :
    trivialCoinvariantsEquiv G A
        (Coinvariants.mk (Rep.trivial ℤ G A).ρ x) = x := by
  rfl

@[simp]
theorem trivialNorm_apply
    (G : Type u) [Group G] [Fintype G]
    (A : Type v) [AddCommGroup A] [Module ℤ A]
    (x : (Rep.trivial ℤ G A).ρ.Coinvariants) :
    trivialInvariantsEquiv G A
        (normCoinvariantsInvariants
          (Rep.trivial ℤ G A) x) =
      Fintype.card G • trivialCoinvariantsEquiv G A x := by
  induction x using Coinvariants.induction_on with
  | _ x =>
      dsimp [trivialInvariantsEquiv,
        trivialCoinvariantsEquiv,
        normCoinvariantsInvariants]
      simp [Representation.norm]

/-- The image of multiplication by `n` in an additive abelian group. -/
def nSRange (n : ℕ) (A : Type v) [AddCommGroup A] :
    AddSubgroup A where
  carrier := {y | ∃ x : A, n • x = y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by simp⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by simp⟩

/-- The kernel of multiplication by `n` in an additive abelian group. -/
def nSKernel (n : ℕ) (A : Type v) [AddCommGroup A] :
    AddSubgroup A where
  carrier := {x | n • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simpa using congrArg₂ (· + ·) hx hy
  neg_mem' := by
    intro x hx
    simpa using congrArg Neg.neg hx

private theorem trivial_norm_range
    (G : Type u) [Group G] [Fintype G]
    (A : Type v) [AddCommGroup A] [Module ℤ A] :
    AddSubgroup.map
        (trivialInvariantsEquiv G A).toAddMonoidHom
        (LinearMap.range
          (normCoinvariantsInvariants
            (Rep.trivial ℤ G A))).toAddSubgroup =
      nSRange (Fintype.card G) A := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx⟩, rfl⟩
    refine ⟨trivialCoinvariantsEquiv G A x, ?_⟩
    rw [← trivialNorm_apply G A x]
    exact congrArg (trivialInvariantsEquiv G A) hx
  · rintro ⟨x, hx⟩
    let q := (trivialCoinvariantsEquiv G A).symm x
    let z := normCoinvariantsInvariants
      (Rep.trivial ℤ G A) q
    refine ⟨z, ⟨q, rfl⟩, ?_⟩
    change trivialInvariantsEquiv G A z = y
    rw [trivialNorm_apply]
    exact hx

/-- For a trivial action, low Tate degree zero is the quotient by
multiplication by the group order. -/
noncomputable def trivialTateEquiv
    (G : Type u) [Group G] [Fintype G]
    (A : Type v) [AddCommGroup A] [Module ℤ A] :
    tateZero (Rep.trivial ℤ G A) ≃+
      A ⧸ nSRange (Fintype.card G) A :=
  QuotientAddGroup.congr
    (LinearMap.range
      (normCoinvariantsInvariants
        (Rep.trivial ℤ G A))).toAddSubgroup
    (nSRange (Fintype.card G) A)
    (trivialInvariantsEquiv G A)
    (trivial_norm_range G A)

/-- For a trivial action, low Tate degree minus one is the torsion kernel
of multiplication by the group order. -/
noncomputable def trivialTateNeg
    (G : Type u) [Group G] [Fintype G]
    (A : Type v) [AddCommGroup A] [Module ℤ A] :
    tateNegOne (Rep.trivial ℤ G A) ≃+
      nSKernel (Fintype.card G) A where
  toFun x := ⟨trivialCoinvariantsEquiv G A x.1, by
    change Fintype.card G • trivialCoinvariantsEquiv G A x.1 = 0
    rw [← trivialNorm_apply G A x.1]
    rw [x.2]
    rfl⟩
  invFun x := ⟨(trivialCoinvariantsEquiv G A).symm x.1, by
    apply (trivialInvariantsEquiv G A).injective
    rw [trivialNorm_apply]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (trivialCoinvariantsEquiv G A).symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact (trivialCoinvariantsEquiv G A).apply_symm_apply x.1
  map_add' x y := by
    apply Subtype.ext
    exact map_add (trivialCoinvariantsEquiv G A) x.1 y.1

/-- The additive form of the quotient map modulo `n`th powers. -/
noncomputable def powerAddHom
    (n : ℕ) (M : Type v) [CommGroup M] :
    Additive M →+ Additive
      (M ⧸ (powMonoidHom n : M →* M).range) where
  toFun x := Additive.ofMul
    (QuotientGroup.mk' (powMonoidHom n : M →* M).range x.toMul)
  map_zero' := by simp
  map_add' x y := by
    apply Additive.toMul.injective
    exact map_mul (QuotientGroup.mk'
      (powMonoidHom n : M →* M).range) x.toMul y.toMul

theorem add_hom_surjective
    (n : ℕ) (M : Type v) [CommGroup M] :
    Function.Surjective (powerAddHom n M) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom n : M →* M).range x.toMul
  exact ⟨Additive.ofMul y, rfl⟩

theorem add_hom_ker
    (n : ℕ) (M : Type v) [CommGroup M] :
    (powerAddHom n M).ker =
      nSRange n (Additive M) := by
  ext x
  constructor
  · intro hx
    change QuotientGroup.mk'
      (powMonoidHom n : M →* M).range x.toMul = 1 at hx
    have hx' : x.toMul ∈ (powMonoidHom n : M →* M).range :=
      (QuotientGroup.eq_one_iff _).mp hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨Additive.ofMul y, ?_⟩
    exact congrArg Additive.ofMul hy
  · rintro ⟨y, hy⟩
    change QuotientGroup.mk'
      (powMonoidHom n : M →* M).range x.toMul = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    refine ⟨y.toMul, ?_⟩
    exact congrArg Additive.toMul hy

/-- Additive quotient by `nM` and multiplicative quotient by `n`th powers
have the same underlying finite-index group. -/
noncomputable def nSPower
    (n : ℕ) (M : Type v) [CommGroup M] :
    Additive M ⧸ nSRange n (Additive M) ≃+
      Additive (M ⧸ (powMonoidHom n : M →* M).range) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (add_hom_ker n M).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (powerAddHom n M)
        (add_hom_surjective n M))

/-- Additive `n`-torsion and the kernel of the multiplicative `n`th-power
map are canonically the same group. -/
noncomputable def nSMul
    (n : ℕ) (M : Type v) [CommGroup M] :
    nSKernel n (Additive M) ≃+
      Additive (powMonoidHom n : M →* M).ker where
  toFun x := Additive.ofMul ⟨x.1.toMul, by
    change x.1.toMul ^ n = 1
    exact congrArg Additive.toMul x.2⟩
  invFun x := ⟨Additive.ofMul x.toMul.1, by
    exact congrArg Additive.ofMul x.toMul.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private theorem cyclic_trivial_card (n : ℕ) [NeZero n] :
    Fintype.card (Multiplicative (ZMod n)) = n := by
  simp

/-- The Tate-zero group of the trivial cyclic action is the actual power
class group. -/
noncomputable def cyclicTrivialQuotient
    (n : ℕ) [NeZero n] (M : Type v) [CommGroup M] :
    tateZero
        (Rep.trivial ℤ (Multiplicative (ZMod n)) (Additive M)) ≃+
      Additive (M ⧸ (powMonoidHom n : M →* M).range) := by
  let e := trivialTateEquiv
    (Multiplicative (ZMod n)) (Additive M)
  rw [cyclic_trivial_card] at e
  exact e.trans (nSPower n M)

/-- The Tate-minus-one group of the trivial cyclic action is the actual
power-map kernel. -/
noncomputable def cyclicTrivialTate
    (n : ℕ) [NeZero n] (M : Type v) [CommGroup M] :
    tateNegOne
        (Rep.trivial ℤ (Multiplicative (ZMod n)) (Additive M)) ≃+
      Additive (powMonoidHom n : M →* M).ker := by
  let e := trivialTateNeg
    (Multiplicative (ZMod n)) (Additive M)
  rw [cyclic_trivial_card] at e
  exact e.trans (nSMul n M)

/-- Version of the Tate-zero identification for any finite group whose
cardinality is the displayed integer. -/
noncomputable def trivialZeroCard
    (G : Type u) [Group G] [Fintype G] (n : ℕ)
    (hcard : Fintype.card G = n)
    (M : Type v) [CommGroup M] :
    tateZero (Rep.trivial ℤ G (Additive M)) ≃+
      Additive (M ⧸ (powMonoidHom n : M →* M).range) := by
  let e := trivialTateEquiv G (Additive M)
  rw [hcard] at e
  exact e.trans (nSPower n M)

/-- Version of the Tate-minus-one identification for any finite group whose
cardinality is the displayed integer. -/
noncomputable def trivialTateCard
    (G : Type u) [Group G] [Fintype G] (n : ℕ)
    (hcard : Fintype.card G = n)
    (M : Type v) [CommGroup M] :
    tateNegOne (Rep.trivial ℤ G (Additive M)) ≃+
      Additive (powMonoidHom n : M →* M).ker := by
  let e := trivialTateNeg G (Additive M)
  rw [hcard] at e
  exact e.trans (nSMul n M)

/-- A multiplicative subgroup, regarded as an additive subgroup after
passing to `Additive`. -/
def additiveSubgroup
    (M : Type v) [CommGroup M] (H : Subgroup M) :
    AddSubgroup (Additive M) where
  carrier := {x | x.toMul ∈ H}
  zero_mem' := H.one_mem
  add_mem' := fun hx hy ↦ H.mul_mem hx hy
  neg_mem' := fun hx ↦ H.inv_mem hx

/-- The additive form of the quotient map by a multiplicative subgroup. -/
noncomputable def subgroupClassHom
    (M : Type v) [CommGroup M] (H : Subgroup M) :
    Additive M →+ Additive (M ⧸ H) where
  toFun x := Additive.ofMul (QuotientGroup.mk' H x.toMul)
  map_zero' := by simp
  map_add' x y := by
    apply Additive.toMul.injective
    exact map_mul (QuotientGroup.mk' H) x.toMul y.toMul

theorem subgroup_hom_surjective
    (M : Type v) [CommGroup M] (H : Subgroup M) :
    Function.Surjective (subgroupClassHom M H) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective H x.toMul
  exact ⟨Additive.ofMul y, rfl⟩

theorem subgroup_hom_ker
    (M : Type v) [CommGroup M] (H : Subgroup M) :
    (subgroupClassHom M H).ker =
      additiveSubgroup M H := by
  ext x
  change QuotientGroup.mk' H x.toMul = 1 ↔ x.toMul ∈ H
  exact QuotientGroup.eq_one_iff x.toMul

/-- The ordinary multiplicative quotient and its additive presentation are
canonically equivalent. -/
noncomputable def additiveSubgroupEquiv
    (M : Type v) [CommGroup M] (H : Subgroup M) :
    Additive M ⧸ additiveSubgroup M H ≃+
      Additive (M ⧸ H) :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (subgroup_hom_ker M H).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (subgroupClassHom M H)
        (subgroup_hom_surjective M H))

/-- Inclusion of a subgroup, written additively. -/
def subgroupAddInclusion
    (M : Type v) [CommGroup M] (H : Subgroup M) :
    Additive H →+ Additive M where
  toFun x := Additive.ofMul x.toMul.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Inclusion of a subgroup as a morphism of trivial cyclic
representations. -/
noncomputable def trivialRepInclusion
    (G : Type u) [Group G]
    (M : Type v) [CommGroup M] (H : Subgroup M) :
    Rep.trivial ℤ G (Additive H) ⟶ Rep.trivial ℤ G (Additive M) := by
  apply Rep.ofHom
  refine ⟨(subgroupAddInclusion M H).toIntLinearMap, ?_⟩
  intro g
  apply LinearMap.ext
  intro x
  rfl

@[reducible]
private noncomputable def trivial_rep_inclusion
    (G : Type u) [Group G]
    (M : Type v) [CommGroup M] (H : Subgroup M) :
    Finite ↑(kernel (trivialRepInclusion G M H) :
      Rep ℤ G) := by
  let f := trivialRepInclusion G M H
  letI : Mono f := (Rep.mono_iff_injective f).2 fun x y hxy ↦ by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Additive.toMul hxy
  have hzero : IsZero (kernel f) := isZero_kernel_of_mono f
  letI : Subsingleton ↑(kernel f : Rep ℤ G) := by
    constructor
    intro x y
    have hid : 𝟙 (kernel f) = 0 := hzero.eq_of_src _ _
    have hx := congrArg (fun q : kernel f ⟶ kernel f ↦ q.hom x) hid
    have hy := congrArg (fun q : kernel f ⟶ kernel f ↦ q.hom y) hid
    change x = 0 at hx
    change y = 0 at hy
    exact hx.trans hy.symm
  infer_instance

@[reducible]
private noncomputable def trivial_rep_cokernel
    (G : Type u) [Group G]
    (M : Type v) [CommGroup M] (H : Subgroup M)
    [Finite (M ⧸ H)] :
    Finite ↑(cokernel (trivialRepInclusion G M H) :
      Rep ℤ G) := by
  let f := trivialRepInclusion G M H
  let π := cokernel.π f
  letI : Module ℤ (cokernel f : Rep ℤ G) :=
    (cokernel f : Rep ℤ G).hV2
  let φ : Additive M →+
      (cokernel f : Rep ℤ G) :=
    π.hom.toAddMonoidHom
  have hH : additiveSubgroup M H ≤ φ.ker := by
    intro x hx
    let y : Additive H := Additive.ofMul ⟨x.toMul, hx⟩
    have hc := congrArg
      (fun q : (Rep.trivial ℤ G (Additive H)) ⟶
          (cokernel f : Rep ℤ G) ↦ q.hom y)
      (cokernel.condition f)
    change φ x = 0
    exact hc
  let qφ := QuotientAddGroup.lift
    (additiveSubgroup M H) φ hH
  have hsurj : Function.Surjective qφ := by
    intro y
    obtain ⟨x, hx⟩ :=
      (Rep.epi_iff_surjective π).1 (inferInstance : Epi π) y
    refine ⟨QuotientAddGroup.mk'
      (additiveSubgroup M H) x, ?_⟩
    exact hx
  letI : Finite
      (Additive M ⧸ additiveSubgroup M H) :=
    Finite.of_equiv (Additive (M ⧸ H))
      (additiveSubgroupEquiv M H).symm.toEquiv
  exact Finite.of_surjective qφ hsurj

/-- Passing between finite-index subgroups does not change Milne's
`h_n`: this is Corollary II.3.9 applied to the trivial cyclic action. -/
theorem card_ratio_index
    (n : ℕ) (hn : 0 < n) (M : Type v) [CommGroup M] (H : Subgroup M)
    [Finite (M ⧸ H)]
    [Finite (H ⧸ (powMonoidHom n : H →* H).range)]
    [Finite (powMonoidHom n : H →* H).ker] :
    (Nat.card (M ⧸ (powMonoidHom n : M →* M).range) : ℚ) /
        Nat.card (powMonoidHom n : M →* M).ker =
      (Nat.card (H ⧸ (powMonoidHom n : H →* H).range) : ℚ) /
        Nat.card (powMonoidHom n : H →* H).ker := by
  letI : NeZero n := ⟨hn.ne'⟩
  let G := Multiplicative (ZMod n)
  letI : Fintype G := Fintype.ofFinite G
  letI : CommGroup G := IsCyclic.commGroup
  have hGcard : Fintype.card G = n := by
    rw [Fintype.card_eq_nat_card]
    exact (Nat.card_congr (Multiplicative.toAdd : G ≃ ZMod n)).trans
      (Nat.card_zmod n)
  let RH := Rep.trivial ℤ G (Additive H)
  let RM := Rep.trivial ℤ G (Additive M)
  let eH0 := trivialZeroCard
    G n hGcard H
  let eH1 := trivialTateCard
    G n hGcard H
  let eM0 := trivialZeroCard
    G n hGcard M
  let eM1 := trivialTateCard
    G n hGcard M
  letI : Finite (tateZero RH) :=
    Finite.of_equiv
      (Additive (H ⧸ (powMonoidHom n : H →* H).range)) eH0.symm.toEquiv
  letI : Finite (tateNegOne RH) :=
    Finite.of_equiv (Additive (powMonoidHom n : H →* H).ker)
      eH1.symm.toEquiv
  let q : ℚ :=
    (Nat.card (H ⧸ (powMonoidHom n : H →* H).range) : ℚ) /
      Nat.card (powMonoidHom n : H →* H).ker
  have hH : HerbrandQuotientValue RH q := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    change (Nat.card (tateZero RH) : ℚ) /
      Nat.card (tateNegOne RH) = q
    rw [Nat.card_congr eH0.toEquiv, Nat.card_congr eH1.toEquiv]
    rw [Nat.card_congr (Additive.toMul :
      Additive (H ⧸ (powMonoidHom n : H →* H).range) ≃
        (H ⧸ (powMonoidHom n : H →* H).range))]
    rw [Nat.card_congr (Additive.toMul :
      Additive (powMonoidHom n : H →* H).ker ≃
        (powMonoidHom n : H →* H).ker)]
  let f := trivialRepInclusion G M H
  let hker := trivial_rep_inclusion G M H
  let hcoker := trivial_rep_cokernel G M H
  have hM : HerbrandQuotientValue RM q :=
    (Submission.CField.HQuotie.herbrandIsogenyBridge
      G RH RM f hker hcoker q).mp hH
  letI : Finite (tateZero RM) := hM.1
  letI : Finite (tateNegOne RM) := hM.2.1
  have hratio := hM.2.2
  change (Nat.card (tateZero RM) : ℚ) /
      Nat.card (tateNegOne RM) = q at hratio
  rw [Nat.card_congr eM0.toEquiv, Nat.card_congr eM1.toEquiv] at hratio
  rw [Nat.card_congr (Additive.toMul :
    Additive (M ⧸ (powMonoidHom n : M →* M).range) ≃
      (M ⧸ (powMonoidHom n : M →* M).range))] at hratio
  rw [Nat.card_congr (Additive.toMul :
    Additive (powMonoidHom n : M →* M).ker ≃
      (powMonoidHom n : M →* M).ker)] at hratio
  exact hratio

private theorem power_range_equiv
    {M N : Type v} [CommGroup M] [CommGroup N]
    (e : M ≃* N) (n : ℕ) :
    Subgroup.map e.toMonoidHom (powMonoidHom n : M →* M).range =
      (powMonoidHom n : N →* N).range := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, by simp⟩
  · rintro ⟨z, rfl⟩
    refine ⟨e.symm z ^ n, ⟨e.symm z, rfl⟩, ?_⟩
    simp

/-- A multiplicative equivalence carries the `n`th-power quotient to the
`n`th-power quotient. -/
noncomputable def powerMulEquiv
    {M N : Type v} [CommGroup M] [CommGroup N]
    (e : M ≃* N) (n : ℕ) :
    M ⧸ (powMonoidHom n : M →* M).range ≃*
      N ⧸ (powMonoidHom n : N →* N).range :=
  QuotientGroup.congr
    (powMonoidHom n : M →* M).range
    (powMonoidHom n : N →* N).range e
    (power_range_equiv e n)

/-- A multiplicative equivalence carries `n`-torsion to `n`-torsion. -/
noncomputable def powerKernelEquiv
    {M N : Type v} [CommGroup M] [CommGroup N]
    (e : M ≃* N) (n : ℕ) :
    (powMonoidHom n : M →* M).ker ≃*
      (powMonoidHom n : N →* N).ker where
  toFun x := ⟨e x.1, by
    change e x.1 ^ n = 1
    rw [← map_pow, show x.1 ^ n = 1 from x.2, map_one]⟩
  invFun x := ⟨e.symm x.1, by
    change e.symm x.1 ^ n = 1
    rw [← map_pow, show x.1 ^ n = 1 from x.2, map_one]⟩
  left_inv x := by ext; exact e.symm_apply_apply x.1
  right_inv x := by ext; exact e.apply_symm_apply x.1
  map_mul' _ _ := by ext; exact map_mul e _ _

end

end Submission.CField.KNIndex
