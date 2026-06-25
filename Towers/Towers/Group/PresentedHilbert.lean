import Mathlib
import Towers.Group.PresentedHighDegree
import Towers.Group.PresentedAugmentationBridge
import Towers.Group.PresentedAugmentationQuotient
import Towers.Group.GolodHilbertData


open Filter
open scoped Pointwise EuclideanGeometry Topology BigOperators

noncomputable section

namespace Towers

universe u
universe v w z

namespace GShafar

/--
Conversely, the second Zassenhaus subgroup is invisible in the elementary
abelian mod-`p` quotient of the free group.

This is the direction needed for arbitrary presentations: a relator whose
Zassenhaus depth is at least two contributes no degree-one linear relation.
-/
theorem mod_abelianization_vector
    {α : Type*} [Fintype α] {p : ℕ} [Fact p.Prime] {w : FreeGroup α}
    (hw : w ∈ zassenhausFiltration p (FreeGroup α) 2) :
    modAbelianizationVector p w = 0 := by
  classical
  let A := MonoidAlgebra (ZMod p) (FreeGroup α)
  let I : Ideal A := augmentationIdeal (R := ZMod p) (G := FreeGroup α)
  have hI2 :
      MonoidAlgebra.of (ZMod p) (FreeGroup α) w - 1 ∈ I ^ (2 : ℕ) := by
    have haug :
        w ∈ augmentationPowerSubgroup (R := ZMod p) (G := FreeGroup α) 2 :=
      (zassenhaus_filtration_subgroup
        (p := p) (G := FreeGroup α) 2) hw
    simpa [augmentationPowerSubgroup, A, I] using haug
  have hker :
      MonoidAlgebra.of (ZMod p) (FreeGroup α) w - 1 ∈
        RingHom.ker
          (freeFirstOrder (α := α) (p := p)).toRingHom := by
    simpa [A, I] using
      (augmentation_sq_order
        (α := α) (p := p) hI2)
  have himage :
      freeFirstOrder (α := α) (p := p)
          (MonoidAlgebra.of (ZMod p) (FreeGroup α) w - 1) = 0 :=
    RingHom.mem_ker.mp hker
  have hinr :
      TrivSqZeroExt.inr (modAbelianizationVector p w) =
        (0 : TrivSqZeroExt (ZMod p) (α →₀ ZMod p)) := by
    simpa using
      (free_relator_difference
        (α := α) (p := p) w).symm.trans himage
  have hsnd :=
    congrArg
      (TrivSqZeroExt.snd : TrivSqZeroExt (ZMod p) (α →₀ ZMod p) → α →₀ ZMod p)
      hinr
  simpa using hsnd

end GShafar


namespace TBluepr

open GShafar

/--
For any group, the degree-zero augmentation layer of `𝔽_p[G]` has dimension
one. This is the quotient `I^0 / I^1 = 𝔽_p[G] / I`, identified with `𝔽_p`
by the augmentation map.
-/
theorem augmentation_finrank_one
    {p : ℕ} [Fact p.Prime] (G : Type) [Group G] :
    let A : Type := MonoidAlgebra (ZMod p) G
    let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
    Module.finrank (ZMod p)
      ((↥((I ^ (0 : ℕ)).restrictScalars (ZMod p))) ⧸
        Submodule.comap
          (Submodule.subtype ((I ^ (0 : ℕ)).restrictScalars (ZMod p)))
          ((I ^ (1 : ℕ)).restrictScalars (ZMod p))) = 1 := by
  classical
  let A : Type := MonoidAlgebra (ZMod p) G
  let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
  let I0 : Submodule (ZMod p) A := (I ^ (0 : ℕ)).restrictScalars (ZMod p)
  let I1 : Submodule (ZMod p) A := (I ^ (1 : ℕ)).restrictScalars (ZMod p)
  let K : Submodule (ZMod p) I0 := I1.comap (Submodule.subtype I0)
  let augLinear : A →ₗ[ZMod p] ZMod p :=
    (GShafar.augmentationHom (ZMod p) G).toLinearMap
  let aug0 : I0 →ₗ[ZMod p] ZMod p := augLinear.comp (Submodule.subtype I0)
  have hker : LinearMap.ker aug0 = K := by
    ext x
    constructor
    · intro hx
      have hxI : (x : A) ∈ I := by
        have hxaug : (GShafar.augmentationHom (ZMod p) G).toRingHom (x : A) = 0 := by
          simpa [aug0, augLinear] using hx
        exact RingHom.mem_ker.mpr hxaug
      change (x : A) ∈ I1
      change (x : A) ∈ (I ^ (1 : ℕ)).restrictScalars (ZMod p)
      change (x : A) ∈ (I ^ (1 : ℕ) : Submodule A A)
      simpa [Submodule.pow_one] using hxI
    · intro hx
      have hxI : (x : A) ∈ I := by
        have hxI1 : (x : A) ∈ I1 := hx
        change (x : A) ∈ (I ^ (1 : ℕ)).restrictScalars (ZMod p) at hxI1
        change (x : A) ∈ (I ^ (1 : ℕ) : Submodule A A) at hxI1
        simpa [Submodule.pow_one] using hxI1
      have hxaug :
          (GShafar.augmentationHom (ZMod p) G).toRingHom (x : A) = 0 :=
        RingHom.mem_ker.mp hxI
      change aug0 x = 0
      simpa [aug0, augLinear] using hxaug
  have hsurj : Function.Surjective aug0 := by
    intro c
    have hmem : (c • (1 : A)) ∈ I0 := by
      change (c • (1 : A)) ∈ (I ^ (0 : ℕ)).restrictScalars (ZMod p)
      change (c • (1 : A)) ∈ (I ^ (0 : ℕ) : Submodule A A)
      rw [Submodule.pow_zero]
      simp
    refine ⟨⟨c • (1 : A), hmem⟩, ?_⟩
    simp [aug0, augLinear]
  let e : ((↥I0) ⧸ K) ≃ₗ[ZMod p] ZMod p :=
    (Submodule.quotEquivOfEq K (LinearMap.ker aug0) hker.symm).trans
      (aug0.quotKerEquivOfSurjective hsurj)
  have hfinrank :
      Module.finrank (ZMod p) ((↥I0) ⧸ K) = 1 := by
    calc
      Module.finrank (ZMod p) ((↥I0) ⧸ K)
          = Module.finrank (ZMod p) (ZMod p) :=
            LinearEquiv.finrank_eq e
      _ = 1 := CommSemiring.finrank_self (ZMod p)
  change Module.finrank (ZMod p) ((↥I0) ⧸ K) = 1
  exact hfinrank

/--
If the `n`th power of the augmentation ideal is zero, then the `n`th
associated-graded augmentation layer has dimension zero.
-/
theorem augmentation_finrank_bot
    {p : ℕ} [Fact p.Prime] (G : Type) [Group G] {n : ℕ}
    (hpow :
      (let A : Type := MonoidAlgebra (ZMod p) G
       let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
       I ^ n = ⊥)) :
    let A : Type := MonoidAlgebra (ZMod p) G
    let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
    Module.finrank (ZMod p)
      ((↥((I ^ n).restrictScalars (ZMod p))) ⧸
        Submodule.comap
          (Submodule.subtype ((I ^ n).restrictScalars (ZMod p)))
          ((I ^ (n + 1)).restrictScalars (ZMod p))) = 0 := by
  classical
  let A : Type := MonoidAlgebra (ZMod p) G
  let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
  let In1 : Submodule (ZMod p) A := (I ^ (n + 1)).restrictScalars (ZMod p)
  change I ^ n = ⊥ at hpow
  change Module.finrank (ZMod p)
      ((↥((I ^ n).restrictScalars (ZMod p))) ⧸
        Submodule.comap (Submodule.subtype ((I ^ n).restrictScalars (ZMod p))) In1) = 0
  rw [hpow]
  let K : Submodule (ZMod p) (↥(⊥ : Submodule (ZMod p) A)) :=
    Submodule.comap (Submodule.subtype (⊥ : Submodule (ZMod p) A)) In1
  change Module.finrank (ZMod p) ((↥(⊥ : Submodule (ZMod p) A)) ⧸ K) = 0
  haveI : Subsingleton ((↥(⊥ : Submodule (ZMod p) A)) ⧸ K) := inferInstance
  exact (Module.finrank_zero_iff
    (R := ZMod p) (M := ((↥(⊥ : Submodule (ZMod p) A)) ⧸ K))).2 inferInstance

/--
The augmentation-layer Hilbert sequence of the concrete presented group algebra.

Naming this sequence is important: the coefficient inequality must be proved
for these actual associated-graded pieces, not for an arbitrary sequence that
only happens to have positive constant term and finite support.
-/
noncomputable def presentedHilbertSequence
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) : ℕ → ℕ :=
  fun n =>
    let G : Type := PresentedGroup (Set.range rels)
    let A : Type := MonoidAlgebra (ZMod p) G
    let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
    Module.finrank (ZMod p)
      ((↥((I ^ n).restrictScalars (ZMod p))) ⧸
        Submodule.comap
          (Submodule.subtype ((I ^ n).restrictScalars (ZMod p)))
          ((I ^ (n + 1)).restrictScalars (ZMod p)))

/--
The quadratic augmentation quotient is spanned by its scalar part and its
degree-one augmentation layer.

Concretely, every class `x mod I²` is represented as
`aug(x) • 1 + (x - aug(x) • 1)`, where the second summand lies in `I`.  This
gives a surjection `𝔽_p × I/I² → A/I²`, hence the dimension bound below.  This
is exactly the finite-dimensional bookkeeping needed to turn the first-order
model lower bound on `A/I²` into a lower bound on the degree-one layer.
-/
theorem sq_finrank_layer
    {p : ℕ} [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    let A : Type := MonoidAlgebra (ZMod p) G
    let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
    Module.finrank (ZMod p) (A ⧸ I ^ (2 : ℕ)) ≤
      1 +
        Module.finrank (ZMod p)
          ((↥((I ^ (1 : ℕ)).restrictScalars (ZMod p))) ⧸
            Submodule.comap
              (Submodule.subtype ((I ^ (1 : ℕ)).restrictScalars (ZMod p)))
              ((I ^ (2 : ℕ)).restrictScalars (ZMod p))) := by
  classical
  let A : Type := MonoidAlgebra (ZMod p) G
  let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
  let I1 : Submodule (ZMod p) A := (I ^ (1 : ℕ)).restrictScalars (ZMod p)
  let I2 : Submodule (ZMod p) A := (I ^ (2 : ℕ)).restrictScalars (ZMod p)
  let K : Submodule (ZMod p) I1 := I2.comap (Submodule.subtype I1)
  let q : A →ₗ[ZMod p] A ⧸ I ^ (2 : ℕ) :=
    (Ideal.Quotient.mkₐ (ZMod p) (I ^ (2 : ℕ))).toLinearMap
  let layerToQuot0 : I1 →ₗ[ZMod p] A ⧸ I ^ (2 : ℕ) :=
    q.comp (Submodule.subtype I1)
  have hlayer_ker : K ≤ LinearMap.ker layerToQuot0 := by
    intro x hx
    change layerToQuot0 x = 0
    change Ideal.Quotient.mk _ (x : A) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.2
    have hxI2 : (x : A) ∈ I2 := by
      simpa [K, I2] using hx
    change (x : A) ∈ (I ^ (2 : ℕ)).restrictScalars (ZMod p) at hxI2
    exact
      (Submodule.restrictScalars_mem (ZMod p) (I ^ (2 : ℕ)) (x : A)).mp hxI2
  let layerToQuot : I1 ⧸ K →ₗ[ZMod p] A ⧸ I ^ (2 : ℕ) :=
    K.liftQ layerToQuot0 hlayer_ker
  let scalarToA : ZMod p →ₗ[ZMod p] A :=
    { toFun := fun c => c • (1 : A)
      map_add' := by
        intro c d
        simp [add_smul]
      map_smul' := by
        intro c d
        simp [smul_smul] }
  let scalarToQuot : ZMod p →ₗ[ZMod p] A ⧸ I ^ (2 : ℕ) :=
    q.comp scalarToA
  let source : Type := ZMod p × (I1 ⧸ K)
  let total : source →ₗ[ZMod p] A ⧸ I ^ (2 : ℕ) :=
    scalarToQuot.comp
        (LinearMap.fst (ZMod p) (ZMod p) (I1 ⧸ K)) +
      layerToQuot.comp
        (LinearMap.snd (ZMod p) (ZMod p) (I1 ⧸ K))
  have hsurj : Function.Surjective total := by
    intro z
    rcases Ideal.Quotient.mk_surjective z with ⟨x, rfl⟩
    let c : ZMod p := GShafar.augmentationHom (ZMod p) G x
    let y : A := x - c • (1 : A)
    have hyI : y ∈ I := by
      change y ∈ RingHom.ker (GShafar.augmentationHom (ZMod p) G).toRingHom
      rw [RingHom.mem_ker]
      change GShafar.augmentationHom (ZMod p) G y = 0
      simp [y, c]
    have hyI1 : y ∈ I1 := by
      change y ∈ (I ^ (1 : ℕ)).restrictScalars (ZMod p)
      change y ∈ (I ^ (1 : ℕ) : Submodule A A)
      simp [Submodule.pow_one, hyI]
    let y1 : I1 := ⟨y, hyI1⟩
    refine ⟨(c, K.mkQ y1), ?_⟩
    change scalarToQuot c + layerToQuot (K.mkQ y1) = Ideal.Quotient.mk _ x
    have hlayer :
        layerToQuot (K.mkQ y1) = Ideal.Quotient.mk (I ^ (2 : ℕ)) y := by
      simp [layerToQuot, layerToQuot0, q, y1]
    rw [hlayer]
    change q (c • (1 : A)) + q y = q x
    rw [← map_add]
    congr 1
    simp [y, c, sub_eq_add_neg, add_left_comm]
  haveI : Module.Finite (ZMod p) A := by
    dsimp [A]
    infer_instance
  haveI : Module.Finite (ZMod p) (A ⧸ I ^ (2 : ℕ)) := by
    exact Module.Finite.of_surjective
      (R := ZMod p) (M := A) (P := A ⧸ I ^ (2 : ℕ)) q
      Ideal.Quotient.mk_surjective
  haveI : Module.Finite (ZMod p) I1 := inferInstance
  haveI : Module.Finite (ZMod p) (I1 ⧸ K) := inferInstance
  haveI : Module.Finite (ZMod p) source := inferInstance
  have hle :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_surjective total hsurj)
      (Module.rank_lt_aleph0 (ZMod p) source)
  change Module.finrank (ZMod p) (A ⧸ I ^ (2 : ℕ)) ≤
    1 + Module.finrank (ZMod p) (I1 ⧸ K)
  simpa [source, Module.finrank_prod, CommSemiring.finrank_self, add_comm] using hle

/-
For the final finite-presented `p`-group statement, the honest Hilbert-series
object is the associated-graded augmentation sequence of the finite group
algebra `𝔽_p[G]`.  The two lemmas below isolate the remaining mathematics in
smaller pieces:

* the finite-dimensional augmentation algebra gives a nonnegative sequence with
  positive degree-zero term and finite support;
* the presentation generators and relators give the coefficientwise
  Golod--Shafarevich dimension inequality for that sequence.

Together with the already-proved formal polynomial reductions in the
`GShafar` namespace, these are exactly the classical Hilbert-series
ingredients needed for the target theorem.
-/

/--
The augmentation-layer Hilbert sequence attached to a finite nontrivial
presented `p`-group has positive constant term and finite support.

Mathematically, `b n` is intended to be
`dim_{𝔽_p} I^n / I^{n+1}` for the augmentation ideal `I` of
`𝔽_p[PresentedGroup (range rels)]`.  Positivity at `0` comes from the class of
`1`, and eventual vanishing comes from nilpotence of the augmentation ideal of
a finite `p`-group algebra.
-/
theorem hilbert_sequence_data
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (_depth : Fin r → ℕ)
    (_hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (_depth i))
    (_hdepth2 : ∀ i, 2 ≤ _depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels))) :
    ∃ N : ℕ,
      0 < presentedHilbertSequence (p := p) rels 0 ∧
        (∀ n, N ≤ n →
          presentedHilbertSequence (p := p) rels n = 0) := by
  classical
  let G : Type := PresentedGroup (Set.range rels)
  letI : Group G := by
    dsimp [G]
    infer_instance
  letI : Finite G := by
    dsimp [G]
    infer_instance
  letI : Nontrivial G := by
    dsimp [G]
    infer_instance
  let A : Type := MonoidAlgebra (ZMod p) G
  let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
  have hPGroupG : IsPGroup p G := by
    simpa [G] using hPGroup
  rcases augmentation_nilpotent_group
      p (Fact.out : Nat.Prime p) G hPGroupG with
    ⟨N, hN⟩
  refine ⟨N, ?_, ?_⟩
  · have hb0 : presentedHilbertSequence (p := p) rels 0 = 1 := by
      simpa [presentedHilbertSequence, G, A, I] using
        augmentation_finrank_one (p := p) G
    rw [hb0]
    norm_num
  · intro n hNn
    have hpow : I ^ n = ⊥ := by
      apply le_antisymm
      · calc
          I ^ n ≤ I ^ N := Ideal.pow_le_pow_right hNn
          _ = ⊥ := hN
      · exact bot_le
    simpa [presentedHilbertSequence, G, A, I] using
      augmentation_finrank_bot
        (p := p) G (n := n) (by simpa [A, I] using hpow)

/--
Relators of Zassenhaus depth at least two vanish in the elementary abelian
mod-`p` quotient of the free group.

This is the first-degree input for the arbitrary-presentation case. It is
mathematically smaller than the coefficient inequality: it only identifies
why the degree-one relator correction term is zero.
-/
theorem presented_abelianization_vector
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i) :
    ∀ i, GShafar.modAbelianizationVector p (rels i) = 0 := by
  intro i
  have hD2 :
      rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) 2 := by
    exact
      (zassenhausFiltration_antitone p (FreeGroup (Fin d)) (hdepth2 i))
        (hdepth i)
  exact
    GShafar.mod_abelianization_vector
      hD2

/--
The degree-one augmentation layer has dimension at least the number of
presentation generators.

The relators have no mod-`p` abelianized linear part, so the presented-group
algebra still maps onto the square-zero first-order model on `d` generators.
What remains is the bookkeeping that identifies the non-scalar part of the
quadratic augmentation truncation with the first associated-graded layer.
-/
theorem presented_p_generators
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (_hPGroup : IsPGroup p (PresentedGroup (Set.range rels))) :
    d ≤ presentedHilbertSequence (p := p) rels 1 := by
  classical
  let G : Type := PresentedGroup (Set.range rels)
  let A : Type := MonoidAlgebra (ZMod p) G
  let I : Ideal A := GShafar.augmentationIdeal (ZMod p) G
  have hzero :
      ∀ i, GShafar.modAbelianizationVector p (rels i) = 0 :=
    presented_abelianization_vector
      rels depth hdepth hdepth2
  have hfirstOrder :
      d + 1 ≤
        Module.finrank (ZMod p)
          (A ⧸ I ^ (2 : ℕ)) := by
    simpa [A, I, Fintype.card_fin] using
      finrank_aug_sq
        (α := Fin d) (ι := Fin r) (p := p) (rels := rels) hzero
  have hquot :
      Module.finrank (ZMod p) (A ⧸ I ^ (2 : ℕ)) ≤
        1 + presentedHilbertSequence (p := p) rels 1 := by
    simpa [presentedHilbertSequence, G, A, I] using
      sq_finrank_layer
        (p := p) G
  have hmain :
      d + 1 ≤ 1 + presentedHilbertSequence (p := p) rels 1 :=
    le_trans hfirstOrder hquot
  omega

/--
The positive-degree-one coefficient inequality for the concrete augmentation
Hilbert sequence.

This packages the already-formal arithmetic boundary case separately from the
high-degree generator/relator multiplication estimate.
-/
theorem presented_full_inequality
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels))) :
    GShafar.fullCoefficientInequality d
      (presentedHilbertSequence (p := p) rels) depth 1 := by
  classical
  have hb0 :
      presentedHilbertSequence (p := p) rels 0 = 1 := by
    let G : Type := PresentedGroup (Set.range rels)
    letI : Group G := by
      dsimp [G]
      infer_instance
    simpa [presentedHilbertSequence, G] using
      augmentation_finrank_one (p := p) G
  have hb1 :
      d ≤ presentedHilbertSequence (p := p) rels 1 :=
    presented_p_generators
      rels depth hdepth hdepth2 hPGroup
  have hrel :
      GShafar.fullRelatorTerm
        (presentedHilbertSequence (p := p) rels) depth 1 = 0 :=
    full_depth_two
      (presentedHilbertSequence (p := p) rels) depth hdepth2
  change
    d *
        GShafar.fullNatTerm
          (presentedHilbertSequence (p := p) rels) 1 ≤
      presentedHilbertSequence (p := p) rels 1 +
        GShafar.fullRelatorTerm
          (presentedHilbertSequence (p := p) rels) depth 1
  rw [full_nat_generator, hrel, hb0, mul_one, add_zero]
  exact hb1

/--
The `n`th associated-graded augmentation layer of the concrete presented group
algebra.

This is the type-level version of `presentedHilbertSequence`; naming
it lets the high-degree step be expressed as an honest finite-dimensional
linear-algebra statement.
-/
abbrev presentedGroupAlgebra
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) : Type :=
  MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))

abbrev presentedAugmentationIdeal
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) :
    Ideal (presentedGroupAlgebra (p := p) rels) :=
  GShafar.augmentationIdeal
    (ZMod p)
    (PresentedGroup (Set.range rels))

abbrev presentedAugmentationSubmodule
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ) :
    Submodule (ZMod p) (presentedGroupAlgebra (p := p) rels) :=
  ((presentedAugmentationIdeal (p := p) rels) ^ n).restrictScalars (ZMod p)

abbrev presentedAugmentationKernel
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ) :
    Submodule (ZMod p)
      (presentedAugmentationSubmodule (p := p) rels n) :=
  (presentedAugmentationSubmodule (p := p) rels (n + 1)).comap
    (Submodule.subtype (presentedAugmentationSubmodule (p := p) rels n))

noncomputable abbrev pALayer
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ) : Type :=
  (↥(presentedAugmentationSubmodule (p := p) rels n)) ⧸
    presentedAugmentationKernel (p := p) rels n

noncomputable instance module_presented_layer
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ)
    [Finite (PresentedGroup (Set.range rels))] :
    Module.Finite (ZMod p) (pALayer (p := p) rels n) := by
  change Module.Finite (ZMod p)
    ((↥(presentedAugmentationSubmodule (p := p) rels n)) ⧸
      presentedAugmentationKernel (p := p) rels n)
  infer_instance

noncomputable instance module_free_presented
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ) :
    Module.Free (ZMod p) (pALayer (p := p) rels n) := by
  infer_instance

/--
The named layer has exactly the Hilbert-sequence dimension.
-/
theorem finrank_presented_layer
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ) :
    Module.finrank (ZMod p) (pALayer (p := p) rels n) =
      presentedHilbertSequence (p := p) rels n := by
  rfl

/-- Active relators at coefficient degree `n`. -/
abbrev pARelato {r : ℕ} (depth : Fin r → ℕ) (n : ℕ) :=
  {i : Fin r // depth i ≤ n}

/--
Summing over active relators is the same as summing over all relators with the
usual `if depth i ≤ n then ... else 0` convention.
-/
theorem presented_active_relators
    {r : ℕ} {M : Type*} [AddCommMonoid M]
    (depth : Fin r → ℕ) (n : ℕ)
    (f : Fin r → M) :
    (∑ i : pARelato depth n, f i.1) =
      ∑ i, if depth i ≤ n then f i else 0 := by
  classical
  calc
    (∑ i : pARelato depth n, f i.1) =
        ∑ i ∈ Finset.univ with depth i ≤ n, f i := by
      simpa [pARelato] using
        (Finset.sum_subtype_eq_sum_filter
          (s := Finset.univ)
          (f := f)
          (p := fun i : Fin r => depth i ≤ n))
    _ = ∑ i, if depth i ≤ n then f i else 0 := by
      rw [Finset.sum_filter]

/--
The relator side of the high-degree GS map: one shifted augmentation layer for
each active relator.
-/
noncomputable abbrev pHSrc
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (depth : Fin r → ℕ) (n : ℕ) : Type :=
  ∀ i : pARelato depth n,
    pALayer (p := p) rels (n - depth i.1)

/--
The generator side of the high-degree GS map: `d` copies of the previous
augmentation layer.
-/
noncomputable abbrev pGTarget
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ) : Type :=
  Fin d → pALayer (p := p) rels (n - 1)

/-- The augmentation difference attached to a presentation generator. -/
noncomputable def presentedGeneratorDifference
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (j : Fin d) :
    presentedGroupAlgebra (p := p) rels :=
  augmentationDifference
    (ZMod p)
    (PresentedGroup (Set.range rels))
    (PresentedGroup.of (rels := Set.range rels) j)

/-- Presentation-generator differences lie in the presented augmentation ideal. -/
lemma presented_difference_ideal
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (j : Fin d) :
    presentedGeneratorDifference (p := p) rels j ∈
      presentedAugmentationIdeal (p := p) rels := by
  simpa [presentedGeneratorDifference, presentedAugmentationIdeal] using
    augmentation_difference_ideal
      (ZMod p)
      (PresentedGroup (Set.range rels))
      (PresentedGroup.of (rels := Set.range rels) j)

/--
The degree-one classes of the presentation-generator differences span `I/I^2`.

This is the generator-only fact that the quotient group presented by `rels` is
generated by the images of the free generators.
-/
theorem presented_classes_top
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    [Finite (PresentedGroup (Set.range rels))] :
    Submodule.span (ZMod p)
      (Set.range fun j : Fin d =>
        augmentationDegreeClass
          (ZMod p)
          (PresentedGroup (Set.range rels))
          (PresentedGroup.of (rels := Set.range rels) j)) =
      ⊤ := by
  classical
  let G : Type := PresentedGroup (Set.range rels)
  have hall :
      Submodule.span (ZMod p)
        (Set.range fun g : G =>
          augmentationDegreeClass (ZMod p) G g) =
        ⊤ :=
    augmentation_span_top (ZMod p) G
  apply le_antisymm
  · exact le_top
  · rw [← hall]
    refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with ⟨g, rfl⟩
    have hg :
        g ∈ Subgroup.closure
          (Set.range
            (PresentedGroup.of :
              Fin d → PresentedGroup (Set.range rels))) := by
      rw [PresentedGroup.closure_range_of (Set.range rels)]
      exact Subgroup.mem_top g
    exact
      span_range_closure
        (ZMod p)
        (PresentedGroup (Set.range rels))
        (Fin d)
        (fun j : Fin d => PresentedGroup.of (rels := Set.range rels) j)
        hg

/--
Presentation-generator differences left-generate the augmentation ideal modulo
`I^2`.
-/
theorem differences_modulo_square
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    [Finite (PresentedGroup (Set.range rels))] :
    augmentationModuloSquare
      (ZMod p)
      (PresentedGroup (Set.range rels))
      (Fin d)
      (presentedGeneratorDifference (p := p) rels) := by
  classical
  let genDiff : Fin d → presentedGroupAlgebra (p := p) rels :=
    presentedGeneratorDifference (p := p) rels
  have hgen :
      ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels := by
    intro j
    exact presented_difference_ideal (p := p) rels j
  have hspanClass :
      Submodule.span (ZMod p)
        (Set.range fun j : Fin d =>
          augmentationDegreeMk
            (ZMod p)
            (PresentedGroup (Set.range rels))
            (genDiff j)
            (hgen j)) =
        ⊤ := by
    simpa [genDiff, presentedGeneratorDifference, augmentationDegreeMk,
      augmentationDegreeClass] using
      presented_classes_top (p := p) rels
  exact
    modulo_square_span
      (ZMod p)
      (PresentedGroup (Set.range rels))
      (Fin d)
      genDiff
      hgen
      hspanClass

/--
A numerator-level form of generation in degree `n`.

Every element of `I^n` is, modulo `I^(n+1)`, a finite sum of left products of
the chosen degree-one generator differences with elements of `I^(n-1)`.
-/
def presentedAugmentationGenerated
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (_hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (_hn : 1 ≤ n) : Prop :=
  ∀ x : presentedAugmentationSubmodule (p := p) rels n,
    ∃ y : Fin d →
        presentedAugmentationSubmodule (p := p) rels (n - 1),
      (x : presentedGroupAlgebra (p := p) rels) -
          ∑ j, genDiff j *
            ((y j :
              presentedAugmentationSubmodule (p := p) rels (n - 1)) :
              presentedGroupAlgebra (p := p) rels) ∈
        presentedAugmentationSubmodule (p := p) rels (n + 1)

/--
Degree-one generation modulo `I^2` propagates to every positive power of the
augmentation ideal.
-/
theorem presented_gen_square
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hleft :
      augmentationModuloSquare
        (ZMod p)
        (PresentedGroup (Set.range rels))
        (Fin d)
        genDiff) :
    presentedAugmentationGenerated
      (p := p) rels genDiff hgen n hn := by
  classical
  let A := presentedGroupAlgebra (p := p) rels
  let I : Ideal A := presentedAugmentationIdeal (p := p) rels
  haveI : I.IsTwoSided := by
    change (presentedAugmentationIdeal (p := p) rels).IsTwoSided
    dsimp [presentedAugmentationIdeal, GShafar.augmentationIdeal]
    infer_instance
  intro x
  have hxmul : (x : A) ∈ I * I ^ (n - 1) := by
    have hxpow : (x : A) ∈ I ^ n := by
      simp [I, presentedAugmentationSubmodule]
    have hdegree : 1 + (n - 1) = n := by omega
    have hpow : I ^ n = I * I ^ (n - 1) := by
      calc
        I ^ n = I ^ (1 + (n - 1)) := by rw [hdegree]
        _ = I ^ 1 * I ^ (n - 1) := by rw [Ideal.IsTwoSided.pow_add]
        _ = I * I ^ (n - 1) := by rw [Submodule.pow_one]
    simpa [hpow] using hxpow
  let P : A → Prop := fun z =>
    ∃ y : Fin d →
        presentedAugmentationSubmodule (p := p) rels (n - 1),
      z - ∑ j, genDiff j *
        ((y j : presentedAugmentationSubmodule (p := p) rels (n - 1)) :
          A) ∈ I ^ (n + 1)
  have hxP : P (x : A) := by
    refine Submodule.mul_induction_on hxmul ?mul_mem ?add_mem
    · intro a ha b hb
      rcases hleft a (by simpa [I] using ha) with ⟨coeff, hcoeff⟩
      let y : Fin d →
          presentedAugmentationSubmodule (p := p) rels (n - 1) :=
        fun j => ⟨coeff j * b, (I ^ (n - 1)).mul_mem_left (coeff j) hb⟩
      refine ⟨y, ?_⟩
      have hsum_mul :
          (∑ j, genDiff j * coeff j) * b =
            ∑ j, genDiff j *
              ((y j :
                presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                A) := by
        dsimp [y]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [mul_assoc]
      have herr_eq :
          a * b -
              ∑ j, genDiff j *
                ((y j :
                  presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                  A) =
            (a - ∑ j, genDiff j * coeff j) * b := by
        rw [← hsum_mul]
        noncomm_ring
      rw [herr_eq]
      have herr_prod :
          (a - ∑ j, genDiff j * coeff j) * b ∈
          I ^ (2 : ℕ) * I ^ (n - 1) :=
        Ideal.mul_mem_mul (by simpa [I] using hcoeff) hb
      have hdegree : (2 : ℕ) + (n - 1) = n + 1 := by omega
      rw [← hdegree, Ideal.IsTwoSided.pow_add]
      exact herr_prod
    · intro u v hu hv
      rcases hu with ⟨yu, hyu⟩
      rcases hv with ⟨yv, hyv⟩
      let y : Fin d →
          presentedAugmentationSubmodule (p := p) rels (n - 1) :=
        fun j => yu j + yv j
      refine ⟨y, ?_⟩
      have hsum_add :
          ∑ j, genDiff j *
              ((y j :
                presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                A) =
            (∑ j, genDiff j *
              ((yu j :
                presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                A)) +
            (∑ j, genDiff j *
              ((yv j :
                presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                A)) := by
        dsimp [y]
        simp [mul_add, Finset.sum_add_distrib]
      have herr_eq :
          u + v -
              ∑ j, genDiff j *
                ((y j :
                  presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                  A) =
            (u -
              ∑ j, genDiff j *
                ((yu j :
                  presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                  A)) +
            (v -
              ∑ j, genDiff j *
                ((yv j :
                  presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                  A)) := by
        rw [hsum_add]
        noncomm_ring
      rw [herr_eq]
      exact (I ^ (n + 1)).add_mem hyu hyv
  simpa [presentedAugmentationGenerated, P, I,
    presentedAugmentationSubmodule] using hxP

/-- Left multiplication by an element of `I^m` sends `I^n` into `I^(m+n)`. -/
lemma presented_augmentation_left
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n : ℕ}
    {a : presentedGroupAlgebra (p := p) rels}
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m)
    (x : presentedAugmentationSubmodule (p := p) rels n) :
    a * (x : presentedGroupAlgebra (p := p) rels) ∈
      presentedAugmentationSubmodule (p := p) rels (m + n) := by
  let I : Ideal (presentedGroupAlgebra (p := p) rels) :=
    presentedAugmentationIdeal (p := p) rels
  haveI : I.IsTwoSided := by
    change (presentedAugmentationIdeal (p := p) rels).IsTwoSided
    dsimp [presentedAugmentationIdeal, GShafar.augmentationIdeal]
    infer_instance
  have hx : (x : presentedGroupAlgebra (p := p) rels) ∈ I ^ n := by
    simp [I, presentedAugmentationSubmodule]
  have hprod :
      a * (x : presentedGroupAlgebra (p := p) rels) ∈ I ^ m * I ^ n :=
    Ideal.mul_mem_mul (by simpa [I] using ha) hx
  have htarget :
      a * (x : presentedGroupAlgebra (p := p) rels) ∈ I ^ (m + n) := by
    rw [Ideal.IsTwoSided.pow_add]
    exact hprod
  simpa [I, presentedAugmentationSubmodule] using htarget

/-- The filtered left-multiplication map with target degree rewritten to `k`. -/
noncomputable def presentedAugmentationLeft
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : m + n = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m) :
    presentedAugmentationSubmodule (p := p) rels n →ₗ[ZMod p]
      presentedAugmentationSubmodule (p := p) rels k where
  toFun x :=
    ⟨a * (x : presentedGroupAlgebra (p := p) rels),
      by
        have hx :
            a * (x : presentedGroupAlgebra (p := p) rels) ∈
              presentedAugmentationSubmodule (p := p) rels (m + n) :=
          presented_augmentation_left
            (p := p) (rels := rels) (m := m) (n := n) ha x
        simpa [hdegree] using hx⟩
  map_add' x y := by
    ext
    simp [mul_add]
  map_smul' c x := by
    ext
    simp

@[simp]
lemma presented_left_mul
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : m + n = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m)
    (x : presentedAugmentationSubmodule (p := p) rels n) :
    (presentedAugmentationLeft
        (p := p) (rels := rels) (m := m) (n := n) (k := k)
        hdegree a ha x :
        presentedGroupAlgebra (p := p) rels) =
      a * (x : presentedGroupAlgebra (p := p) rels) := rfl

/-- The target-degree rewritten multiplication map respects layer kernels. -/
lemma presented_layer_kernel
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : m + n = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m)
    {x : presentedAugmentationSubmodule (p := p) rels n}
    (hx : x ∈ presentedAugmentationKernel (p := p) rels n) :
    presentedAugmentationLeft
        (p := p) (rels := rels) (m := m) (n := n) (k := k)
        hdegree a ha x ∈
      presentedAugmentationKernel (p := p) rels k := by
  let I : Ideal (presentedGroupAlgebra (p := p) rels) :=
    presentedAugmentationIdeal (p := p) rels
  haveI : I.IsTwoSided := by
    change (presentedAugmentationIdeal (p := p) rels).IsTwoSided
    dsimp [presentedAugmentationIdeal, GShafar.augmentationIdeal]
    infer_instance
  have hxpow : (x : presentedGroupAlgebra (p := p) rels) ∈ I ^ (n + 1) := by
    simpa [I, presentedAugmentationKernel,
      presentedAugmentationSubmodule] using hx
  have hprod :
      a * (x : presentedGroupAlgebra (p := p) rels) ∈ I ^ m * I ^ (n + 1) :=
    Ideal.mul_mem_mul (by simpa [I] using ha) hxpow
  have htarget :
      a * (x : presentedGroupAlgebra (p := p) rels) ∈ I ^ (k + 1) := by
    have hdegree' : m + (n + 1) = k + 1 := by omega
    rw [← hdegree', Ideal.IsTwoSided.pow_add]
    exact hprod
  simpa [I, presentedAugmentationKernel, presentedAugmentationSubmodule,
    presentedAugmentationLeft] using htarget

/-- The associated-graded left-multiplication map induced by an element of `I^m`. -/
noncomputable def presentedLeftMul
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : m + n = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m) :
    pALayer (p := p) rels n →ₗ[ZMod p]
      pALayer (p := p) rels k :=
  (presentedAugmentationKernel (p := p) rels n).mapQ
    (presentedAugmentationKernel (p := p) rels k)
    (presentedAugmentationLeft
      (p := p) (rels := rels) (m := m) (n := n) (k := k)
      hdegree a ha)
    (by
      intro x hx
      exact presented_layer_kernel
        (p := p) (rels := rels) (m := m) (n := n) (k := k)
        hdegree a ha hx)

@[simp]
lemma presented_left_mk
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : m + n = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m)
    (x : presentedAugmentationSubmodule (p := p) rels n) :
    presentedLeftMul
        (p := p) (rels := rels) (m := m) (n := n) (k := k)
        hdegree a ha
        ((presentedAugmentationKernel (p := p) rels n).mkQ x) =
      (presentedAugmentationKernel (p := p) rels k).mkQ
        (presentedAugmentationLeft
          (p := p) (rels := rels) (m := m) (n := n) (k := k)
          hdegree a ha x) := rfl

/--
The high-degree multiplication map attached to a chosen list of degree-one
augmentation elements.
-/
noncomputable def presentedGeneratorMultiplication
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (hn : 1 ≤ n) :
    pGTarget (p := p) rels n →ₗ[ZMod p]
      pALayer (p := p) rels n :=
  LinearMap.lsum (ZMod p)
    (fun _ : Fin d =>
      pALayer (p := p) rels (n - 1))
    (ZMod p)
    (fun j =>
      presentedLeftMul
        (p := p) (rels := rels)
        (m := 1) (n := n - 1) (k := n)
        (by omega)
        (genDiff j)
        (by
          simpa [Submodule.pow_one] using hgen j))

/--
Numerator-level generation implies surjectivity of the descended
associated-graded generator multiplication map.
-/
theorem presented_multiplication_surjective
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hspan :
      presentedAugmentationGenerated
        (p := p) rels genDiff hgen n hn) :
    Function.Surjective
      (presentedGeneratorMultiplication
        (p := p) rels genDiff hgen n hn) := by
  classical
  intro z
  rcases (presentedAugmentationKernel (p := p) rels n).mkQ_surjective z with
    ⟨x, rfl⟩
  rcases hspan x with ⟨y, hy⟩
  let yLayer : pGTarget (p := p) rels n :=
    fun j =>
      (presentedAugmentationKernel (p := p) rels (n - 1)).mkQ (y j)
  let hdegree : 1 + (n - 1) = n := by omega
  let yProduct : Fin d →
      presentedAugmentationSubmodule (p := p) rels n :=
    fun j =>
      presentedAugmentationLeft
        (p := p) (rels := rels)
        (m := 1) (n := n - 1) (k := n) hdegree
        (genDiff j)
        (by simpa [Submodule.pow_one] using hgen j)
        (y j)
  let s : presentedAugmentationSubmodule (p := p) rels n :=
    ∑ j, yProduct j
  let K := presentedAugmentationKernel (p := p) rels n
  refine ⟨yLayer, ?_⟩
  have hmap :
      presentedGeneratorMultiplication
          (p := p) rels genDiff hgen n hn yLayer =
        K.mkQ s := by
    have hβsum :
        presentedGeneratorMultiplication
            (p := p) rels genDiff hgen n hn yLayer =
          ∑ j, K.mkQ (yProduct j) := by
      dsimp [presentedGeneratorMultiplication, yLayer]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      apply Finset.sum_congr rfl
      intro j _hj
      dsimp [yProduct, K]
      exact presented_left_mk
        (p := p) (rels := rels)
        (m := 1) (n := n - 1) (k := n) hdegree
        (genDiff j)
        (by simpa [Submodule.pow_one] using hgen j)
        (y j)
    have hsum :
        (∑ j, K.mkQ (yProduct j)) = K.mkQ s := by
      dsimp [s]
      exact (map_sum K.mkQ yProduct Finset.univ).symm
    exact hβsum.trans hsum
  have hsval :
      (s : presentedGroupAlgebra (p := p) rels) =
        ∑ j, genDiff j *
          ((y j :
            presentedAugmentationSubmodule (p := p) rels (n - 1)) :
            presentedGroupAlgebra (p := p) rels) := by
    dsimp [s, yProduct]
    simp
  have hkernel :
      x - s ∈ presentedAugmentationKernel (p := p) rels n := by
    change ((x - s :
        presentedAugmentationSubmodule (p := p) rels n) :
        presentedGroupAlgebra (p := p) rels) ∈
      presentedAugmentationSubmodule (p := p) rels (n + 1)
    simpa [sub_eq_add_neg, hsval] using hy
  have hkernel' :
      s - x ∈ presentedAugmentationKernel (p := p) rels n := by
    rw [← neg_sub]
    exact (presentedAugmentationKernel (p := p) rels n).neg_mem hkernel
  rw [hmap]
  exact (Submodule.Quotient.eq (presentedAugmentationKernel (p := p) rels n)).mpr
    hkernel'

/--
Presentation-generator differences right-generate the augmentation ideal modulo
`I^2`.
-/
theorem differences_generate_modulo
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    [Finite (PresentedGroup (Set.range rels))] :
    generatedModuloSquare
      (ZMod p)
      (PresentedGroup (Set.range rels))
      (Fin d)
      (presentedGeneratorDifference (p := p) rels) := by
  classical
  let genDiff : Fin d → presentedGroupAlgebra (p := p) rels :=
    presentedGeneratorDifference (p := p) rels
  have hgen :
      ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels := by
    intro j
    exact presented_difference_ideal (p := p) rels j
  have hspanClass :
      Submodule.span (ZMod p)
        (Set.range fun j : Fin d =>
          augmentationDegreeMk
            (ZMod p)
            (PresentedGroup (Set.range rels))
            (genDiff j)
            (hgen j)) =
        ⊤ := by
    simpa [genDiff, presentedGeneratorDifference, augmentationDegreeMk,
      augmentationDegreeClass] using
      presented_classes_top (p := p) rels
  exact
    generated_modulo_square
      (ZMod p)
      (PresentedGroup (Set.range rels))
      (Fin d)
      genDiff
      hgen
      hspanClass

/--
Right-oriented numerator-level generation in degree `n`.

Every element of `I^n` is, modulo `I^(n+1)`, a finite sum of right products of
elements of `I^(n-1)` with the chosen degree-one generator differences.
-/
def presentedGeneratedDegree
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (_hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (_hn : 1 ≤ n) : Prop :=
  ∀ x : presentedAugmentationSubmodule (p := p) rels n,
    ∃ y : Fin d →
        presentedAugmentationSubmodule (p := p) rels (n - 1),
      (x : presentedGroupAlgebra (p := p) rels) -
          ∑ j,
            ((y j :
              presentedAugmentationSubmodule (p := p) rels (n - 1)) :
              presentedGroupAlgebra (p := p) rels) *
              genDiff j ∈
        presentedAugmentationSubmodule (p := p) rels (n + 1)

/--
Right degree-one generation modulo `I^2` propagates to every positive
augmentation power.
-/
theorem presented_aug_square
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hright :
      generatedModuloSquare
        (ZMod p)
        (PresentedGroup (Set.range rels))
        (Fin d)
        genDiff) :
    presentedGeneratedDegree
      (p := p) rels genDiff hgen n hn := by
  classical
  let A := presentedGroupAlgebra (p := p) rels
  let I : Ideal A := presentedAugmentationIdeal (p := p) rels
  haveI : I.IsTwoSided := by
    change (presentedAugmentationIdeal (p := p) rels).IsTwoSided
    dsimp [presentedAugmentationIdeal, GShafar.augmentationIdeal]
    infer_instance
  intro x
  have hxmul : (x : A) ∈ I ^ (n - 1) * I := by
    have hxpow : (x : A) ∈ I ^ n := by
      simp [I, presentedAugmentationSubmodule]
    have hdegree : (n - 1) + 1 = n := by omega
    have hpow : I ^ n = I ^ (n - 1) * I := by
      calc
        I ^ n = I ^ ((n - 1) + 1) := by rw [hdegree]
        _ = I ^ (n - 1) * I ^ 1 := by rw [Ideal.IsTwoSided.pow_add]
        _ = I ^ (n - 1) * I := by rw [Submodule.pow_one]
    simpa [hpow] using hxpow
  let P : A → Prop := fun z =>
    ∃ y : Fin d →
        presentedAugmentationSubmodule (p := p) rels (n - 1),
      z - ∑ j,
        ((y j : presentedAugmentationSubmodule (p := p) rels (n - 1)) :
          A) * genDiff j ∈ I ^ (n + 1)
  have hxP : P (x : A) := by
    refine Submodule.mul_induction_on hxmul ?mul_mem ?add_mem
    · intro a ha b hb
      rcases hright b (by simpa [I] using hb) with ⟨coeff, hcoeff⟩
      let y : Fin d →
          presentedAugmentationSubmodule (p := p) rels (n - 1) :=
        fun j => ⟨a * coeff j, (I ^ (n - 1)).mul_mem_right (coeff j) ha⟩
      refine ⟨y, ?_⟩
      have hmul_sum :
          a * (∑ j, coeff j * genDiff j) =
            ∑ j,
              ((y j :
                presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                A) * genDiff j := by
        dsimp [y]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [mul_assoc]
      have herr_eq :
          a * b -
              ∑ j,
                ((y j :
                  presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                  A) * genDiff j =
            a * (b - ∑ j, coeff j * genDiff j) := by
        rw [← hmul_sum]
        noncomm_ring
      rw [herr_eq]
      have herr_prod :
          a * (b - ∑ j, coeff j * genDiff j) ∈
            I ^ (n - 1) * I ^ (2 : ℕ) :=
        Ideal.mul_mem_mul ha (by simpa [I] using hcoeff)
      have hdegree : (n - 1) + (2 : ℕ) = n + 1 := by omega
      rw [← hdegree, Ideal.IsTwoSided.pow_add]
      exact herr_prod
    · intro u v hu hv
      rcases hu with ⟨yu, hyu⟩
      rcases hv with ⟨yv, hyv⟩
      let y : Fin d →
          presentedAugmentationSubmodule (p := p) rels (n - 1) :=
        fun j => yu j + yv j
      refine ⟨y, ?_⟩
      have hsum_add :
          ∑ j,
              ((y j :
                presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                A) * genDiff j =
            (∑ j,
              ((yu j :
                presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                A) * genDiff j) +
            (∑ j,
              ((yv j :
                presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                A) * genDiff j) := by
        dsimp [y]
        simp [add_mul, Finset.sum_add_distrib]
      have herr_eq :
          u + v -
              ∑ j,
                ((y j :
                  presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                  A) * genDiff j =
            (u -
              ∑ j,
                ((yu j :
                  presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                  A) * genDiff j) +
            (v -
              ∑ j,
                ((yv j :
                  presentedAugmentationSubmodule (p := p) rels (n - 1)) :
                  A) * genDiff j) := by
        rw [hsum_add]
        noncomm_ring
      rw [herr_eq]
      exact (I ^ (n + 1)).add_mem hyu hyv
  simpa [presentedGeneratedDegree, P, I,
    presentedAugmentationSubmodule] using hxP

/-- Right multiplication by an element of `I^m` sends `I^n` into `I^(n+m)`. -/
lemma presented_right_mul
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n : ℕ}
    {a : presentedGroupAlgebra (p := p) rels}
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m)
    (x : presentedAugmentationSubmodule (p := p) rels n) :
    (x : presentedGroupAlgebra (p := p) rels) * a ∈
      presentedAugmentationSubmodule (p := p) rels (n + m) := by
  let I : Ideal (presentedGroupAlgebra (p := p) rels) :=
    presentedAugmentationIdeal (p := p) rels
  haveI : I.IsTwoSided := by
    change (presentedAugmentationIdeal (p := p) rels).IsTwoSided
    dsimp [presentedAugmentationIdeal, GShafar.augmentationIdeal]
    infer_instance
  have hx : (x : presentedGroupAlgebra (p := p) rels) ∈ I ^ n := by
    simp [I, presentedAugmentationSubmodule]
  have hprod :
      (x : presentedGroupAlgebra (p := p) rels) * a ∈ I ^ n * I ^ m :=
    Ideal.mul_mem_mul hx (by simpa [I] using ha)
  have htarget :
      (x : presentedGroupAlgebra (p := p) rels) * a ∈ I ^ (n + m) := by
    rw [Ideal.IsTwoSided.pow_add]
    exact hprod
  simpa [I, presentedAugmentationSubmodule] using htarget

/-- The filtered right-multiplication map with target degree rewritten to `k`. -/
noncomputable def presentedRightMul
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : n + m = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m) :
    presentedAugmentationSubmodule (p := p) rels n →ₗ[ZMod p]
      presentedAugmentationSubmodule (p := p) rels k where
  toFun x :=
    ⟨(x : presentedGroupAlgebra (p := p) rels) * a,
      by
        have hx :
            (x : presentedGroupAlgebra (p := p) rels) * a ∈
              presentedAugmentationSubmodule (p := p) rels (n + m) :=
          presented_right_mul
            (p := p) (rels := rels) (m := m) (n := n) ha x
        simpa [hdegree] using hx⟩
  map_add' x y := by
    ext
    simp [add_mul]
  map_smul' c x := by
    ext
    simp

@[simp]
lemma presented_augmentation_mul
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : n + m = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m)
    (x : presentedAugmentationSubmodule (p := p) rels n) :
    (presentedRightMul
        (p := p) (rels := rels) (m := m) (n := n) (k := k)
        hdegree a ha x :
        presentedGroupAlgebra (p := p) rels) =
      (x : presentedGroupAlgebra (p := p) rels) * a := rfl

/-- The target-degree rewritten right-multiplication map respects layer kernels. -/
lemma presented_augmentation_kernel
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : n + m = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m)
    {x : presentedAugmentationSubmodule (p := p) rels n}
    (hx : x ∈ presentedAugmentationKernel (p := p) rels n) :
    presentedRightMul
        (p := p) (rels := rels) (m := m) (n := n) (k := k)
        hdegree a ha x ∈
      presentedAugmentationKernel (p := p) rels k := by
  let I : Ideal (presentedGroupAlgebra (p := p) rels) :=
    presentedAugmentationIdeal (p := p) rels
  haveI : I.IsTwoSided := by
    change (presentedAugmentationIdeal (p := p) rels).IsTwoSided
    dsimp [presentedAugmentationIdeal, GShafar.augmentationIdeal]
    infer_instance
  have hxpow : (x : presentedGroupAlgebra (p := p) rels) ∈ I ^ (n + 1) := by
    simpa [I, presentedAugmentationKernel,
      presentedAugmentationSubmodule] using hx
  have hprod :
      (x : presentedGroupAlgebra (p := p) rels) * a ∈ I ^ (n + 1) * I ^ m :=
    Ideal.mul_mem_mul hxpow (by simpa [I] using ha)
  have htarget :
      (x : presentedGroupAlgebra (p := p) rels) * a ∈ I ^ (k + 1) := by
    have hdegree' : (n + 1) + m = k + 1 := by omega
    rw [← hdegree', Ideal.IsTwoSided.pow_add]
    exact hprod
  simpa [I, presentedAugmentationKernel, presentedAugmentationSubmodule,
    presentedRightMul] using htarget

/-- The associated-graded right-multiplication map induced by an element of `I^m`. -/
noncomputable def presentedAugmentationMul
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : n + m = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m) :
    pALayer (p := p) rels n →ₗ[ZMod p]
      pALayer (p := p) rels k :=
  (presentedAugmentationKernel (p := p) rels n).mapQ
    (presentedAugmentationKernel (p := p) rels k)
    (presentedRightMul
      (p := p) (rels := rels) (m := m) (n := n) (k := k)
      hdegree a ha)
    (by
      intro x hx
      exact presented_augmentation_kernel
        (p := p) (rels := rels) (m := m) (n := n) (k := k)
        hdegree a ha hx)

@[simp]
lemma presented_augmentation_mk
    {p d r : ℕ} [Fact p.Prime]
    {rels : Fin r → FreeGroup (Fin d)}
    {m n k : ℕ}
    (hdegree : n + m = k)
    (a : presentedGroupAlgebra (p := p) rels)
    (ha : a ∈ (presentedAugmentationIdeal (p := p) rels) ^ m)
    (x : presentedAugmentationSubmodule (p := p) rels n) :
    presentedAugmentationMul
        (p := p) (rels := rels) (m := m) (n := n) (k := k)
        hdegree a ha
        ((presentedAugmentationKernel (p := p) rels n).mkQ x) =
      (presentedAugmentationKernel (p := p) rels k).mkQ
        (presentedRightMul
          (p := p) (rels := rels) (m := m) (n := n) (k := k)
          hdegree a ha x) := rfl

/--
The right-oriented high-degree multiplication map.  This is the orientation
compatible with the Fox syzygy `sum_j (∂r/∂x_j)(x_j-1)=0`.
-/
noncomputable def highDegreeMultiplication
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (hn : 1 ≤ n) :
    pGTarget (p := p) rels n →ₗ[ZMod p]
      pALayer (p := p) rels n :=
  LinearMap.lsum (ZMod p)
    (fun _ : Fin d =>
      pALayer (p := p) rels (n - 1))
    (ZMod p)
    (fun j =>
      presentedAugmentationMul
        (p := p) (rels := rels)
        (m := 1) (n := n - 1) (k := n)
        (by omega)
        (genDiff j)
        (by
          simpa [Submodule.pow_one] using hgen j))

/-- The right-oriented generator multiplication map on representatives. -/
lemma presented_multiplication_mk
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (hn : 1 ≤ n)
    (y : Fin d →
      presentedAugmentationSubmodule (p := p) rels (n - 1)) :
    highDegreeMultiplication
        (p := p) rels genDiff hgen n hn
        (fun j =>
          (presentedAugmentationKernel (p := p) rels (n - 1)).mkQ (y j)) =
      (presentedAugmentationKernel (p := p) rels n).mkQ
        (∑ j,
          presentedRightMul
            (p := p) (rels := rels)
            (m := 1) (n := n - 1) (k := n)
            (by omega)
            (genDiff j)
            (by simpa [Submodule.pow_one] using hgen j)
            (y j)) := by
  let K := presentedAugmentationKernel (p := p) rels n
  calc
    highDegreeMultiplication
        (p := p) rels genDiff hgen n hn
        (fun j =>
          (presentedAugmentationKernel (p := p) rels (n - 1)).mkQ (y j))
        =
        ∑ j,
          K.mkQ
            (presentedRightMul
              (p := p) (rels := rels)
              (m := 1) (n := n - 1) (k := n)
              (by omega)
              (genDiff j)
              (by simpa [Submodule.pow_one] using hgen j)
              (y j)) := by
          dsimp [highDegreeMultiplication, K]
          simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
          apply Finset.sum_congr rfl
          intro j _hj
          exact presented_augmentation_mk
            (p := p) (rels := rels)
            (m := 1) (n := n - 1) (k := n)
            (by omega)
            (genDiff j)
            (by simpa [Submodule.pow_one] using hgen j)
            (y j)
    _ =
        K.mkQ
          (∑ j,
            presentedRightMul
              (p := p) (rels := rels)
              (m := 1) (n := n - 1) (k := n)
              (by omega)
              (genDiff j)
              (by simpa [Submodule.pow_one] using hgen j)
              (y j)) := by
          exact (map_sum K.mkQ
            (fun j =>
              presentedRightMul
                (p := p) (rels := rels)
                (m := 1) (n := n - 1) (k := n)
                (by omega)
                (genDiff j)
                (by simpa [Submodule.pow_one] using hgen j)
                (y j))
            Finset.univ).symm

/--
Right-oriented numerator-level generation implies surjectivity of the
right-oriented associated-graded generator multiplication map.
-/
theorem presented_multiplication_gen
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (genDiff : Fin d → presentedGroupAlgebra (p := p) rels)
    (hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hspan :
      presentedGeneratedDegree
        (p := p) rels genDiff hgen n hn) :
    Function.Surjective
      (highDegreeMultiplication
        (p := p) rels genDiff hgen n hn) := by
  classical
  intro z
  rcases (presentedAugmentationKernel (p := p) rels n).mkQ_surjective z with
    ⟨x, rfl⟩
  rcases hspan x with ⟨y, hy⟩
  let yLayer : pGTarget (p := p) rels n :=
    fun j =>
      (presentedAugmentationKernel (p := p) rels (n - 1)).mkQ (y j)
  let hdegree : (n - 1) + 1 = n := by omega
  let yProduct : Fin d →
      presentedAugmentationSubmodule (p := p) rels n :=
    fun j =>
      presentedRightMul
        (p := p) (rels := rels)
        (m := 1) (n := n - 1) (k := n) hdegree
        (genDiff j)
        (by simpa [Submodule.pow_one] using hgen j)
        (y j)
  let s : presentedAugmentationSubmodule (p := p) rels n :=
    ∑ j, yProduct j
  let K := presentedAugmentationKernel (p := p) rels n
  refine ⟨yLayer, ?_⟩
  have hmap :
      highDegreeMultiplication
          (p := p) rels genDiff hgen n hn yLayer =
        K.mkQ s := by
    have hβsum :
        highDegreeMultiplication
            (p := p) rels genDiff hgen n hn yLayer =
          ∑ j, K.mkQ (yProduct j) := by
      dsimp [highDegreeMultiplication, yLayer]
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      apply Finset.sum_congr rfl
      intro j _hj
      dsimp [yProduct, K]
      exact presented_augmentation_mk
        (p := p) (rels := rels)
        (m := 1) (n := n - 1) (k := n) hdegree
        (genDiff j)
        (by simpa [Submodule.pow_one] using hgen j)
        (y j)
    have hsum :
        (∑ j, K.mkQ (yProduct j)) = K.mkQ s := by
      dsimp [s]
      exact (map_sum K.mkQ yProduct Finset.univ).symm
    exact hβsum.trans hsum
  have hsval :
      (s : presentedGroupAlgebra (p := p) rels) =
        ∑ j,
          ((y j :
            presentedAugmentationSubmodule (p := p) rels (n - 1)) :
            presentedGroupAlgebra (p := p) rels) *
            genDiff j := by
    dsimp [s, yProduct]
    simp
  have hkernel :
      x - s ∈ presentedAugmentationKernel (p := p) rels n := by
    change ((x - s :
        presentedAugmentationSubmodule (p := p) rels n) :
        presentedGroupAlgebra (p := p) rels) ∈
      presentedAugmentationSubmodule (p := p) rels (n + 1)
    simpa [sub_eq_add_neg, hsval] using hy
  have hkernel' :
      s - x ∈ presentedAugmentationKernel (p := p) rels n := by
    rw [← neg_sub]
    exact (presentedAugmentationKernel (p := p) rels n).neg_mem hkernel
  rw [hmap]
  exact (Submodule.Quotient.eq (presentedAugmentationKernel (p := p) rels n)).mpr
    hkernel'

/-- The concrete right-oriented presentation-generator multiplication map. -/
noncomputable def presentedHighMultiplication
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (n : ℕ)
    (hn : 1 ≤ n) :
    pGTarget (p := p) rels n →ₗ[ZMod p]
      pALayer (p := p) rels n :=
  highDegreeMultiplication
    (p := p)
    rels
    (presentedGeneratorDifference (p := p) rels)
    (fun j => presented_difference_ideal (p := p) rels j)
    n
    hn

/-- The concrete right-oriented presentation-generator multiplication map is surjective. -/
theorem presented_high_multiplication
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (hn : 1 ≤ n) :
    Function.Surjective
      (presentedHighMultiplication
        (p := p) rels n hn) := by
  let genDiff : Fin d → presentedGroupAlgebra (p := p) rels :=
    presentedGeneratorDifference (p := p) rels
  have hgen : ∀ j, genDiff j ∈ presentedAugmentationIdeal (p := p) rels := by
    intro j
    exact presented_difference_ideal (p := p) rels j
  have hright :
      generatedModuloSquare
        (ZMod p)
        (PresentedGroup (Set.range rels))
        (Fin d)
        genDiff := by
    simpa [genDiff] using
      differences_generate_modulo (p := p) rels
  have hspan :
      presentedGeneratedDegree
        (p := p) rels genDiff hgen n hn :=
    presented_aug_square
      (p := p) rels genDiff hgen n hn hright
  simpa [presentedHighMultiplication,
    genDiff, hgen] using
    presented_multiplication_gen
      (p := p) rels genDiff hgen n hn hspan

/-- The quotient map sends free-group augmentation differences to presented ones. -/
lemma presented_free_difference
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (g : FreeGroup (Fin d)) :
    GShafar.presentedAlgebra (R := ZMod p) (Set.range rels)
        (augmentationDifference (ZMod p) (FreeGroup (Fin d)) g) =
      augmentationDifference
        (ZMod p)
        (PresentedGroup (Set.range rels))
        (PresentedGroup.mk (Set.range rels) g) := by
  simpa [GShafar.presentedAlgebra] using
    domain_ring_difference
      (ZMod p)
      (FreeGroup (Fin d))
      (PresentedGroup (Set.range rels))
      (PresentedGroup.mk (Set.range rels))
      g

/-- The quotient map sends `x_j - 1` to the presented generator difference. -/
lemma presented_algebra_difference
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (j : Fin d) :
    GShafar.presentedAlgebra (R := ZMod p) (Set.range rels)
        (augmentationDifference
          (ZMod p)
          (FreeGroup (Fin d))
          (FreeGroup.of j)) =
      presentedGeneratorDifference (p := p) rels j := by
  simpa [presentedGeneratorDifference, PresentedGroup.of] using
    presented_free_difference (p := p) rels (FreeGroup.of j)

/-- A defining relator has zero augmentation difference in the presented algebra. -/
lemma presented_difference_zero
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (i : Fin r) :
    GShafar.presentedAlgebra (R := ZMod p) (Set.range rels)
        (augmentationDifference
          (ZMod p)
          (FreeGroup (Fin d))
          (rels i)) =
      0 := by
  rw [presented_free_difference (p := p) rels (rels i)]
  have hrel :
      PresentedGroup.mk (Set.range rels) (rels i) = 1 :=
    PresentedGroup.one_of_mem (rels := Set.range rels) ⟨i, rfl⟩
  simp [hrel, augmentationDifference, MonoidAlgebra.one_def]

/--
The Fox identity for a defining relator after passing to the presented group
algebra.
-/
theorem presented_relator_syzygy
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (i : Fin r) :
    ∑ j,
        GShafar.presentedAlgebra (R := ZMod p) (Set.range rels)
          (groupFoxDerivative (ZMod p) j (rels i)) *
          presentedGeneratorDifference (p := p) rels j =
      0 := by
  classical
  let R := ZMod p
  let F := FreeGroup (Fin d)
  let A := presentedGroupAlgebra (p := p) rels
  let q : MonoidAlgebra R F →+* A :=
    GShafar.presentedAlgebra (R := R) (Set.range rels)
  have hmap_sum :
      q (∑ j,
          groupFoxDerivative R j (rels i) *
            augmentationDifference R F (FreeGroup.of j)) =
        ∑ j,
          q (groupFoxDerivative R j (rels i)) *
            presentedGeneratorDifference (p := p) rels j := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_mul]
    rw [presented_algebra_difference]
  have hfox :
      augmentationDifference R F (rels i) =
        ∑ j,
          groupFoxDerivative R j (rels i) *
            augmentationDifference R F (FreeGroup.of j) :=
    free_derivative_fundamental R (rels i)
  calc
    ∑ j,
        GShafar.presentedAlgebra (R := ZMod p) (Set.range rels)
          (groupFoxDerivative (ZMod p) j (rels i)) *
          presentedGeneratorDifference (p := p) rels j
        = q (∑ j,
            groupFoxDerivative R j (rels i) *
              augmentationDifference R F (FreeGroup.of j)) := by
          simpa [R, F, A, q] using hmap_sum.symm
    _ = q (augmentationDifference R F (rels i)) := by
          rw [← hfox]
    _ = 0 := by
          simpa [R, F, A, q] using
            presented_difference_zero
              (p := p)
              rels
              i

/-- The pushed-forward Fox coefficient of a presentation relator. -/
noncomputable def presentedFoxCoefficient
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (i : Fin r)
    (j : Fin d) :
    presentedGroupAlgebra (p := p) rels :=
  GShafar.presentedAlgebra (R := ZMod p) (Set.range rels)
    (groupFoxDerivative (ZMod p) j (rels i))

/-- The Fox syzygy remains zero after left multiplication by any algebra element. -/
theorem presented_fox_syzygy
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (i : Fin r)
    (y : presentedGroupAlgebra (p := p) rels) :
    ∑ j,
        (y * presentedFoxCoefficient (p := p) rels i j) *
          presentedGeneratorDifference (p := p) rels j =
      0 := by
  classical
  have hsyzygy :
      (∑ j,
        presentedFoxCoefficient (p := p) rels i j *
          presentedGeneratorDifference (p := p) rels j) = 0 := by
    simpa [presentedFoxCoefficient] using
      presented_relator_syzygy (p := p) rels i
  calc
    ∑ j,
        (y * presentedFoxCoefficient (p := p) rels i j) *
          presentedGeneratorDifference (p := p) rels j
        =
        ∑ j,
          y *
            (presentedFoxCoefficient (p := p) rels i j *
              presentedGeneratorDifference (p := p) rels j) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [mul_assoc]
    _ =
        y *
          (∑ j,
            presentedFoxCoefficient (p := p) rels i j *
              presentedGeneratorDifference (p := p) rels j) := by
          rw [Finset.mul_sum]
    _ = 0 := by
          rw [hsyzygy, mul_zero]

/-- Fox derivatives lower declared Zassenhaus degree by one in the presented algebra. -/
theorem presented_relator_fox
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    {depth : Fin r → ℕ}
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    (i : Fin r)
    (j : Fin d) :
    presentedFoxCoefficient (p := p) rels i j ∈
      (presentedAugmentationIdeal (p := p) rels) ^ (depth i - 1) := by
  let F := FreeGroup (Fin d)
  have hfree :
      groupFoxDerivative (ZMod p) j (rels i) ∈
        (GShafar.augmentationIdeal (ZMod p) F) ^ (depth i - 1) :=
    fox_derivative_zassenhaus
      (p := p)
      (ι := Fin d)
      (n := depth i)
      (g := rels i)
      (hdepth i)
      (hdepth2 i)
      j
  have hmap :
      GShafar.presentedAlgebra (R := ZMod p) (Set.range rels)
          (groupFoxDerivative (ZMod p) j (rels i)) ∈
        (GShafar.augmentationIdeal (ZMod p)
          (PresentedGroup (Set.range rels))) ^ (depth i - 1) :=
    GShafar.presented_algebra_pow
      (R := ZMod p)
      (α := Fin d)
      (rels := Set.range rels)
      hfree
  simpa [presentedFoxCoefficient, presentedAugmentationIdeal, F] using hmap

/--
The source of the split surjection used for the high-degree coefficient
inequality: the target layer itself, together with the active relator
correction layers.
-/
noncomputable abbrev presentedHighDegree
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (depth : Fin r → ℕ) (n : ℕ) : Type :=
  pALayer (p := p) rels n ×
    pHSrc (p := p) rels depth n

theorem finrank_high_target
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (n : ℕ)
    [Finite (PresentedGroup (Set.range rels))] :
    Module.finrank (ZMod p)
        (pGTarget (p := p) rels n) =
      d * presentedHilbertSequence (p := p) rels (n - 1) := by
  simp [pGTarget, finrank_presented_layer,
    Module.finrank_pi_fintype, Fintype.card_fin]

set_option synthInstance.maxHeartbeats 80000 in
-- The source is a product whose second factor is a dependent Pi of quotient
-- layers, so the additive/module instances need a little more search budget.

theorem finrank_high_source
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d)) (depth : Fin r → ℕ) (n : ℕ)
    [Finite (PresentedGroup (Set.range rels))] :
    Module.finrank (ZMod p)
        (presentedHighDegree (p := p) rels depth n) =
      presentedHilbertSequence (p := p) rels n +
        ∑ i, if depth i ≤ n then
          presentedHilbertSequence (p := p) rels (n - depth i)
        else 0 := by
  classical
  have hactive :
      (∑ i : pARelato depth n,
          presentedHilbertSequence (p := p) rels (n - depth i.1)) =
        ∑ i, if depth i ≤ n then
          presentedHilbertSequence (p := p) rels (n - depth i)
        else 0 :=
    presented_active_relators depth n
      (fun i => presentedHilbertSequence (p := p) rels (n - depth i))
  simp [presentedHighDegree, pHSrc,
    finrank_presented_layer, Module.finrank_prod,
    Module.finrank_pi_fintype, hactive]

/--
Pure dimension-counting form of the high-degree coefficient estimate.

Once the algebraic Golod--Shafarevich map from the target layer plus active
relator layers onto the `d` generator copies is known to be surjective, the
desired numerical inequality is just `finrank target ≤ finrank source`.
-/
theorem high_bound_surjective
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    [Finite (PresentedGroup (Set.range rels))]
    (n : ℕ)
    (Ψ :
      presentedHighDegree (p := p) rels depth n →ₗ[ZMod p]
        pGTarget (p := p) rels n)
    (hΨ : Function.Surjective Ψ) :
    d * presentedHilbertSequence (p := p) rels (n - 1) ≤
      presentedHilbertSequence (p := p) rels n +
        ∑ i, if depth i ≤ n then
          presentedHilbertSequence (p := p) rels (n - depth i)
        else 0 := by
  classical
  have hle :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_surjective Ψ hΨ)
      (Module.rank_lt_aleph0 (ZMod p)
        (presentedHighDegree (p := p) rels depth n))
  rw [finrank_high_target (p := p) rels n,
    finrank_high_source (p := p) rels depth n] at hle
  exact hle

/--
Once the concrete augmentation Hilbert sequence satisfies the full
Golod--Shafarevich coefficient inequalities, the formal polynomial witness
follows.

This isolates the remaining arbitrary-presentation work from the already
formalized Hilbert-series algebra.
-/
theorem coefficientwise_witness_inequalities
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hfull :
      ∀ n, GShafar.fullCoefficientInequality d
        (presentedHilbertSequence (p := p) rels) depth n) :
    GShafar.CoefficientwiseHilbertWitness d r depth := by
  classical
  let b : ℕ → ℕ := presentedHilbertSequence (p := p) rels
  rcases hilbert_sequence_data
      rels depth hdepth hdepth2 hPGroup with
    ⟨N, hb0, hzero⟩
  refine
    GShafar.coefficientwise_hilbert_inequalities
      (d := d) (r := r) (depth := depth)
      (a := fun n => (b n : ℝ)) (N := N) ?_ ?_ ?_
  · intro n
    have hnonneg : (0 : ℝ) ≤ (b n : ℝ) := by
      exact_mod_cast Nat.zero_le (b n)
    exact hnonneg
  · have hpos : (0 : ℝ) < (b 0 : ℝ) := by
      exact_mod_cast hb0
    exact hpos
  · intro n _hn
    exact
      GShafar.recurrence_inequality_nat
        (GShafar.recurrence_inequality_eventually
          (d := d) (b := b) (N := N) (depth := depth)
          hzero (by simpa [b] using hfull n))

theorem gs_full_inequalities
    {p d r : ℕ} [Fact p.Prime]
    (rels : Fin r → FreeGroup (Fin d))
    (depth : Fin r → ℕ)
    (hdepth :
      ∀ i, rels i ∈ zassenhausFiltration p (FreeGroup (Fin d)) (depth i))
    (hdepth2 : ∀ i, 2 ≤ depth i)
    [Finite (PresentedGroup (Set.range rels))]
    [Nontrivial (PresentedGroup (Set.range rels))]
    (hPGroup : IsPGroup p (PresentedGroup (Set.range rels)))
    (hfull :
      ∀ n, GShafar.fullCoefficientInequality d
        (presentedHilbertSequence (p := p) rels) depth n)
    {t : ℝ} (ht0 : 0 < t) (_ht1 : t < 1) :
    0 < GShafar.relatorExpression d r depth t := by
  rcases
      coefficientwise_witness_inequalities
        rels depth hdepth hdepth2 hPGroup hfull with
    ⟨P, hPcoeff, hP0, hprodcoeff⟩
  exact
    GShafar.coefficientwise_hilbert_inequality
      (d := d) (r := r) depth hdepth2 hPcoeff hP0 hprodcoeff t ht0


end TBluepr

end Towers
