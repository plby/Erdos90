import Towers.Group.FinitePGS


open Filter
open scoped Pointwise EuclideanGeometry Topology

noncomputable section

open NumberField

namespace Towers

theorem
    PPDatum.minpres_hilbertseries_coefhilbineq
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
          (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (∀ i, 2 ≤ depth i) →
          ∃ P : Polynomial ℝ,
            (∀ n, 0 ≤ P.coeff n) ∧
            0 < P.coeff 0 ∧
            (∀ n, 0 ≤
              ((GShafar.relatorSeriesPolynomial
                    H.generatorRank H.relationRank depth) * P).coeff n)) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  intro rels depth hrels hmem hdepth t ht0 _ht1
  rcases hwitness hrels hmem hdepth with ⟨P, hPcoeff, hP0, hprodcoeff⟩
  exact
    GShafar.coefficientwise_hilbert_inequality
      (d := H.generatorRank) (r := H.relationRank) depth hdepth hPcoeff hP0 hprodcoeff t ht0

set_option synthInstance.maxHeartbeats 500000 in
-- The presented augmentation quotients require a larger instance-search budget.
/--
The same bridge, but reduced one step further to an explicit truncated
coefficient recursion.

In concrete Hilbert-series applications, the intended sequence is built from
finite-dimensional augmentation or relator-difference quotients. The remaining
frontier is now exactly to prove this recursion for such a sequence.
-/
theorem
    PPDatum.minpres_hilbertseries_bridtrunrecu
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
          (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (∀ i, 2 ≤ depth i) →
          ∃ (N : ℕ) (a : ℕ → ℝ),
            (∀ n, 0 ≤ a n) ∧
            0 < a 0 ∧
            (∀ n, 0 ≤
              GShafar.truncatedSequence a N n
                - (H.generatorRank : ℝ) *
                    (if 1 ≤ n then GShafar.truncatedSequence a N (n - 1) else 0)
                + ∑ i, if depth i ≤ n then
                    GShafar.truncatedSequence a N (n - depth i) else 0)) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  intro rels depth hrels hmem hdepth t ht0 _ht1
  rcases hwitness hrels hmem hdepth with ⟨N, a, ha, ha0, hrec⟩
  exact
    GShafar.expression_truncation_recurrence
      (d := H.generatorRank) (r := H.relationRank) depth hdepth ha ha0 hrec t ht0

/--
The canonical candidate sequence on the presented side: its `n`th term is the
`𝔽_p`-dimension of the augmentation quotient `B / I^(n + 2)`.

The shift by `2` packages the already-formalized degree-`0/1` lower bound into
the constant term of the eventual Hilbert-series sequence.
-/
noncomputable def PPDatum.pres_aug_quotfinrank
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) : ℕ := by
  classical
  let p := H.realizesFiniteNontrivial.p
  let e : PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier :=
    Classical.choice hrels
  letI : Finite (PresentedGroup (Set.range rels)) :=
    Finite.of_equiv H.realizesFiniteNontrivial.carrier e.toEquiv.symm
  let A := MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))
  let J : Ideal A :=
    GShafar.augmentationIdeal (R := ZMod p) (G := PresentedGroup (Set.range rels))
  letI : Module.Finite (ZMod p) A := by
    dsimp [A]
    infer_instance
  letI : Module.Finite (ZMod p) (A ⧸ J ^ (n + 2)) := by
    let q : A →ₗ[ZMod p] A ⧸ J ^ (n + 2) :=
      (Ideal.Quotient.mkₐ (ZMod p) (J ^ (n + 2))).toLinearMap
    exact Module.Finite.of_surjective
      (R := ZMod p) (M := A) (P := A ⧸ J ^ (n + 2)) q Ideal.Quotient.mk_surjective
  exact Module.finrank (ZMod p) (A ⧸ J ^ (n + 2))

/--
The same canonical sequence, but viewed in `ℝ` so that it can be fed directly
into the truncated-coefficient recurrence statement above.
-/
noncomputable abbrev PPDatum.pres_aug_quotsequence
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) :
    ℕ → ℝ :=
  fun n => (H.pres_aug_quotfinrank hrels n : ℝ)

/--
It is enough to prove the truncated Hilbert-series recurrence for the explicit
augmentation-quotient dimension sequence of a minimal presented-group algebra.

This is a sharper remaining frontier than the previous existential reduction:
the candidate sequence is now fixed, and the only missing input is the
coefficientwise recursion for its finite truncations.
-/
theorem
    PPDatum.minpres_hilbseribrid_presaugrecu
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            ∀ n, 0 ≤
              GShafar.truncatedSequence
                  (H.pres_aug_quotsequence (rels := rels) hrels) N n
                - (H.generatorRank : ℝ) *
                    (if 1 ≤ n then
                      GShafar.truncatedSequence
                        (H.pres_aug_quotsequence (rels := rels) hrels) N (n - 1)
                    else 0)
                + ∑ i, if depth i ≤ n then
                    GShafar.truncatedSequence
                      (H.pres_aug_quotsequence (rels := rels) hrels) N (n - depth i)
                  else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine H.minpres_hilbertseries_bridtrunrecu ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hrec⟩
  refine ⟨N, H.pres_aug_quotsequence (rels := rels) hrels, ?_, ?_, ?_⟩
  · intro n
    exact_mod_cast Nat.zero_le (H.pres_aug_quotfinrank (rels := rels) hrels n)
  · have hle :
        H.generatorRank + 1 ≤
          H.pres_aug_quotfinrank (rels := rels) hrels 0 := by
      simpa [PPDatum.pres_aug_quotfinrank] using
        (H.finrankpresaug_powquotge_genrankaddone
          (rels := rels) hrels (n := 2) (by simp))
    have hpos :
        0 < H.pres_aug_quotfinrank (rels := rels) hrels 0 := by
      exact lt_of_lt_of_le (Nat.succ_pos H.generatorRank) hle
    exact_mod_cast hpos
  · simpa using hrec

/-
It is enough to check the presented augmentation-quotient recursion on the
finite coefficient window
`0 ≤ n ≤ N + max 1 (sup depth)`.

This makes the remaining obstruction completely explicit: the open Hilbert-step
is now a finite family of inequalities for the concrete sequence
`n ↦ dim(B / I^(n + 2))`.
-/
set_option linter.style.longLine false in
theorem
    PPDatum.minpres_hilbseripres_augfinrecu
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            ∀ n ≤ N + max 1 (Finset.univ.sup depth), 0 ≤
              GShafar.truncatedSequence
                  (H.pres_aug_quotsequence (rels := rels) hrels) N n
                - (H.generatorRank : ℝ) *
                    (if 1 ≤ n then
                      GShafar.truncatedSequence
                        (H.pres_aug_quotsequence (rels := rels) hrels) N (n - 1)
                    else 0)
                + ∑ i, if depth i ≤ n then
                    GShafar.truncatedSequence
                      (H.pres_aug_quotsequence (rels := rels) hrels) N (n - depth i)
                  else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine H.minpres_hilbseribrid_presaugrecu ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hrec⟩
  refine ⟨N, ?_⟩
  intro n
  by_cases hn : n ≤ N + max 1 (Finset.univ.sup depth)
  · exact hrec n hn
  · have hzero :=
      GShafar.truncation_recurrence_window
        (a := H.pres_aug_quotsequence (rels := rels) hrels)
        (N := N) (d := H.generatorRank) (r := H.relationRank) (depth := depth)
        (n := n) (Nat.lt_of_not_ge hn)
    simp only [mul_ite, mul_zero, ge_iff_le] at hzero ⊢
    rw [hzero]

/-
To finish the Hilbert-series bridge, it is enough to verify a finite family of
explicit dimension inequalities for the concrete presented augmentation
quotients `B / I^(n + 2)`.

This removes the remaining abstraction of `truncatedSequence`: the open step is
now a finite-window linear-algebra statement relating the dimensions of the
quotients `B / I^(k)` indexed by `n`, `n - 1`, and `n - depth i`.
-/
set_option linter.style.longLine false in
theorem
    PPDatum.minpres_hilbserifin_windowdimineq
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            ∀ n ≤ N + max 1 (Finset.univ.sup depth),
              H.generatorRank * (if 1 ≤ n then
                  if n - 1 ≤ N then
                    H.pres_aug_quotfinrank (rels := rels) hrels (n - 1)
                  else 0
                else 0) ≤
                (if n ≤ N then
                    H.pres_aug_quotfinrank (rels := rels) hrels n
                  else 0) +
                  ∑ i, if depth i ≤ n then
                    if n - depth i ≤ N then
                      H.pres_aug_quotfinrank
                        (rels := rels) hrels (n - depth i)
                    else 0
                  else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine H.minpres_hilbseripres_augfinrecu ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hdim⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hdim' :
      (H.generatorRank : ℝ) * (if 1 ≤ n then
            if n - 1 ≤ N then
              (H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) : ℝ)
            else 0
          else 0) ≤
        (if n ≤ N then
              (H.pres_aug_quotfinrank (rels := rels) hrels n : ℝ)
            else 0) +
            ∑ i, if depth i ≤ n then
              if n - depth i ≤ N then
                (H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i) : ℝ)
              else 0
            else 0 := by
    exact_mod_cast hdim n hn
  have hrec' :
      0 ≤
        (if n ≤ N then
            (H.pres_aug_quotfinrank (rels := rels) hrels n : ℝ)
          else 0) -
          (H.generatorRank : ℝ) * (if 1 ≤ n then
            if n - 1 ≤ N then
              (H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) : ℝ)
            else 0
          else 0) +
          ∑ i, if depth i ≤ n then
            if n - depth i ≤ N then
              (H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i) : ℝ)
            else 0
          else 0 := by
    nlinarith
  simpa [PPDatum.pres_aug_quotsequence,
    GShafar.truncatedSequence] using hrec'

/-
It is enough to prove the previous finite-window dimension inequalities by
constructing a surjective linear map whose source and target have exactly the
required quotient dimensions.

This isolates the remaining Hilbert-series step as an explicit finite-dimensional
linear-algebra problem: for each `n` in the active window, choose finite
`𝔽_p`-vector spaces matching the truncated quotient dimensions and surject onto
`generatorRank` copies of the previous one.
-/
set_option linter.style.longLine false in
theorem
    PPDatum.presaug_finwindow_dimineqsurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    {N n : ℕ}
    (X Y : Type*) (Z : Fin H.relationRank → Type*)
    [AddCommGroup X] [Module (ZMod H.realizesFiniteNontrivial.p) X]
    [Module.Free (ZMod H.realizesFiniteNontrivial.p) X]
    [Module.Finite (ZMod H.realizesFiniteNontrivial.p) X]
    [AddCommGroup Y] [Module (ZMod H.realizesFiniteNontrivial.p) Y]
    [Module.Free (ZMod H.realizesFiniteNontrivial.p) Y]
    [Module.Finite (ZMod H.realizesFiniteNontrivial.p) Y]
    [∀ i, AddCommGroup (Z i)] [∀ i, Module (ZMod H.realizesFiniteNontrivial.p) (Z i)]
    [∀ i, Module.Free (ZMod H.realizesFiniteNontrivial.p) (Z i)]
    [∀ i, Module.Finite (ZMod H.realizesFiniteNontrivial.p) (Z i)]
    (hX : Module.finrank (ZMod H.realizesFiniteNontrivial.p) X =
      if n ≤ N then
        H.pres_aug_quotfinrank (rels := rels) hrels n
      else 0)
    (hY : Module.finrank (ZMod H.realizesFiniteNontrivial.p) Y =
      if 1 ≤ n then
        if n - 1 ≤ N then
          H.pres_aug_quotfinrank (rels := rels) hrels (n - 1)
        else 0
      else 0)
    (hZ : ∀ i, Module.finrank (ZMod H.realizesFiniteNontrivial.p) (Z i) =
      if depth i ≤ n then
        if n - depth i ≤ N then
          H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)
        else 0
      else 0)
    (f :
      (X × ∀ i, Z i) →ₗ[ZMod H.realizesFiniteNontrivial.p] (Fin H.generatorRank → Y))
    (hf : Function.Surjective f) :
    H.generatorRank * (if 1 ≤ n then
        if n - 1 ≤ N then
          H.pres_aug_quotfinrank (rels := rels) hrels (n - 1)
        else 0
      else 0) ≤
      (if n ≤ N then
          H.pres_aug_quotfinrank (rels := rels) hrels n
        else 0) +
        ∑ i, if depth i ≤ n then
          if n - depth i ≤ N then
            H.pres_aug_quotfinrank
              (rels := rels) hrels (n - depth i)
          else 0
        else 0 := by
  have hle :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_surjective f hf)
      (Module.rank_lt_aleph0 (ZMod H.realizesFiniteNontrivial.p)
        (X × ∀ i, Z i))
  simpa [Module.finrank_prod, Module.finrank_pi_fintype, hX, hY, hZ, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc, add_comm, add_left_comm, add_assoc] using hle

/--
The concrete presented-side quotient space whose dimension contributes the
`n`th Hilbert-series coefficient: the augmentation quotient `B / I^(n + 2)` of
the presented-group algebra attached to a minimal presentation of `H`.
-/
noncomputable abbrev PPDatum.presentedAugmentationQuotient
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) : Type := by
  classical
  let p := H.realizesFiniteNontrivial.p
  let e : PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier :=
    Classical.choice hrels
  letI : Finite (PresentedGroup (Set.range rels)) :=
    Finite.of_equiv H.realizesFiniteNontrivial.carrier e.toEquiv.symm
  exact
    MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels)) ⧸
      GShafar.augmentationIdeal
        (R := ZMod p) (G := PresentedGroup (Set.range rels)) ^ (n + 2)

/--
At step `n`, only relators with `depth i ≤ n` can contribute to the Golod--
Shafarevich coefficient inequality.
-/
abbrev PPDatum.activeRelators
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (n : ℕ) :=
  {i : Fin H.relationRank // depth i ≤ n}

noncomputable abbrev PPDatum.pres_aug_activesource
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (depth : Fin H.relationRank → ℕ) (n : ℕ) : Type :=
  (H.presentedAugmentationQuotient (rels := rels) hrels n) ×
    (∀ i : PPDatum.activeRelators H depth n,
      H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1))

noncomputable abbrev PPDatum.pres_aug_activetarget
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) : Type :=
  Fin H.generatorRank →
    H.presentedAugmentationQuotient (rels := rels) hrels (n - 1)

/--
Every concrete presented augmentation quotient `B / I^(n + 2)` is a finite
`𝔽_p`-vector space.
-/
noncomputable instance PPDatum.module_finpres_augquot
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) :
    Module.Finite (ZMod H.realizesFiniteNontrivial.p)
      (H.presentedAugmentationQuotient (rels := rels) hrels n) := by
  classical
  let p := H.realizesFiniteNontrivial.p
  let e : PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier :=
    Classical.choice hrels
  letI : Finite (PresentedGroup (Set.range rels)) :=
    Finite.of_equiv H.realizesFiniteNontrivial.carrier e.toEquiv.symm
  let B := MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))
  let J : Ideal B :=
    GShafar.augmentationIdeal (R := ZMod p) (G := PresentedGroup (Set.range rels))
  change Module.Finite (ZMod p) (B ⧸ J ^ (n + 2))
  let q : B →ₗ[ZMod p] B ⧸ J ^ (n + 2) :=
    (Ideal.Quotient.mkₐ (ZMod p) (J ^ (n + 2))).toLinearMap
  exact Module.Finite.of_surjective
    (R := ZMod p) (M := B) (P := B ⧸ J ^ (n + 2)) q Ideal.Quotient.mk_surjective

/--
The named quotient space `presentedAugmentationQuotient` really has the
dimension packaged by `pres_aug_quotfinrank`.
-/
theorem PPDatum.finrank_pres_augquot
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) :
    Module.finrank (ZMod H.realizesFiniteNontrivial.p)
      (H.presentedAugmentationQuotient (rels := rels) hrels n) =
        H.pres_aug_quotfinrank (rels := rels) hrels n := by
  rfl

/--
Summing over the active relators at depth `n` is the same as summing over all
relators with the usual `if depth i ≤ n then ... else 0` truncation.
-/
theorem PPDatum.sum_active_relatorseq
    {M : Type*} [AddCommMonoid M]
    (H : PPDatum)
    (depth : Fin H.relationRank → ℕ) (n : ℕ)
    (f : Fin H.relationRank → M) :
    (∑ i : PPDatum.activeRelators H depth n, f i.1) =
      ∑ i, if depth i ≤ n then f i else 0 := by
  classical
  calc
    (∑ i : PPDatum.activeRelators H depth n, f i.1) =
        ∑ i ∈ Finset.univ with depth i ≤ n, f i := by
      simpa [PPDatum.activeRelators] using
        (Finset.sum_subtype_eq_sum_filter
          (s := Finset.univ)
          (f := f)
          (p := fun i : Fin H.relationRank => depth i ≤ n))
    _ = ∑ i, if depth i ≤ n then f i else 0 := by
      rw [Finset.sum_filter]

/--
Left multiplication by an element of the presented-group algebra descends to a
linear map between any two augmentation quotients whose powers are ordered by
inclusion.
-/
noncomputable def PPDatum.pres_augquot_leftmul
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n m : ℕ) (hm : m ≤ n)
    (a :
      MonoidAlgebra (ZMod H.realizesFiniteNontrivial.p)
        (PresentedGroup (Set.range rels))) :
    H.presentedAugmentationQuotient (rels := rels) hrels n →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.presentedAugmentationQuotient (rels := rels) hrels m := by
  classical
  let p := H.realizesFiniteNontrivial.p
  let e : PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier :=
    Classical.choice hrels
  letI : Finite (PresentedGroup (Set.range rels)) :=
    Finite.of_equiv H.realizesFiniteNontrivial.carrier e.toEquiv.symm
  let A := MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))
  let I : Ideal A :=
    GShafar.augmentationIdeal (R := ZMod p) (G := PresentedGroup (Set.range rels))
  have hpow : I ^ (n + 2) ≤ I ^ (m + 2) := by
    exact Ideal.pow_le_pow_right (Nat.add_le_add_right hm 2)
  let f₀ : A ⧸ I ^ (n + 2) →+* A ⧸ I ^ (m + 2) :=
    Ideal.Quotient.factorPow I (Nat.add_le_add_right hm 2)
  let f : A ⧸ I ^ (n + 2) →ₗ[ZMod p] A ⧸ I ^ (m + 2) :=
    f₀.toAddMonoidHom.toZModLinearMap p
  let q : A ⧸ I ^ (m + 2) := Ideal.Quotient.mk _ a
  let g : A ⧸ I ^ (m + 2) →ₗ[ZMod p] A ⧸ I ^ (m + 2) :=
    { toFun := fun x => q * x
      map_add' := by
        intro x y
        exact mul_add q x y
      map_smul' := by
        intro c x
        rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, (Algebra.commutes c q).symm,
          mul_assoc]
        simp }
  simpa [PPDatum.presentedAugmentationQuotient, p, A, I] using g.comp f

/--
If `a` lies in the `k`th augmentation-ideal power, then left multiplication by
`a` raises the quotient depth by `k`.
-/
noncomputable def PPDatum.presaug_quotleft_mulmempow
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n k : ℕ)
    (a :
      MonoidAlgebra (ZMod H.realizesFiniteNontrivial.p)
        (PresentedGroup (Set.range rels)))
    (ha :
      a ∈ GShafar.augmentationIdeal
        (R := ZMod H.realizesFiniteNontrivial.p)
        (G := PresentedGroup (Set.range rels)) ^ k) :
    H.presentedAugmentationQuotient (rels := rels) hrels n →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.presentedAugmentationQuotient (rels := rels) hrels (n + k) := by
  classical
  let p := H.realizesFiniteNontrivial.p
  let e : PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier :=
    Classical.choice hrels
  letI : Finite (PresentedGroup (Set.range rels)) :=
    Finite.of_equiv H.realizesFiniteNontrivial.carrier e.toEquiv.symm
  let A := MonoidAlgebra (ZMod p) (PresentedGroup (Set.range rels))
  let I : Ideal A :=
    GShafar.augmentationIdeal (R := ZMod p) (G := PresentedGroup (Set.range rels))
  let la : A →ₗ[ZMod p] A :=
    { toFun := fun x => a * x
      map_add' := by
        intro x y
        exact mul_add a x y
      map_smul' := by
        intro c x
        rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← mul_assoc]
        congr 1
        exact (Algebra.commutes (R := ZMod p) (A := A) c a).symm }
  let q : A →ₗ[ZMod p] A ⧸ I ^ (n + k + 2) :=
    (Ideal.Quotient.mkₐ (ZMod p) (I ^ (n + k + 2))).toLinearMap
  let f : A →ₗ[ZMod p] A ⧸ I ^ (n + k + 2) := q.comp la
  let K : Submodule (ZMod p) A := Submodule.restrictScalars (ZMod p) (I ^ (n + 2))
  have hf : K ≤ LinearMap.ker f := by
    intro x hx
    have hxK : x ∈ Submodule.restrictScalars (ZMod p) (I ^ (n + 2)) := by
      simpa [K] using hx
    have hx' : x ∈ I ^ (n + 2) := by
      exact (Submodule.restrictScalars_mem (ZMod p) (I ^ (n + 2)) x).mp hxK
    change Ideal.Quotient.mk _ (a * x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 <| by
      have hmul : a * x ∈ I ^ k * I ^ (n + 2) :=
        Ideal.mul_mem_mul ha hx'
      have hle : I ^ k * I ^ (n + 2) ≤ I ^ (n + k + 2) := by
        calc
          I ^ k * I ^ (n + 2) = I ^ (k + (n + 2)) := by
            rw [Ideal.IsTwoSided.pow_add (I := I) (m := k) (n := n + 2)]
          _ = I ^ (n + k + 2) := by
            rw [Nat.add_assoc, Nat.add_left_comm k n, ← Nat.add_assoc]
          _ ≤ I ^ (n + k + 2) := by
            exact le_rfl
      exact hle hmul
  let fq := K.liftQ f hf
  simpa [PPDatum.presentedAugmentationQuotient, p, A, I, f, q, la, K] using fq

/--
The concrete generator difference `of(j) - 1` in the presented-group algebra.
-/
noncomputable def PPDatum.pres_aug_gendifference
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (j : Fin H.generatorRank) :
    MonoidAlgebra (ZMod H.realizesFiniteNontrivial.p)
      (PresentedGroup (Set.range rels)) := by
  exact
    MonoidAlgebra.of (ZMod H.realizesFiniteNontrivial.p) (PresentedGroup (Set.range rels))
        (PresentedGroup.of j) - 1

/--
The type of the generator-side component maps in the eventual
Golod--Shafarevich linear map.

For the intended application, `Γ j` should be multiplication by the generator
difference `of(j) - 1`, descending from `B / I^(n + 2)` to `B / I^(n + 1)`.
-/
abbrev PPDatum.pres_aug_gencomponents
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) :=
  ∀ _ : Fin H.generatorRank,
    H.presentedAugmentationQuotient (rels := rels) hrels n →ₗ[ZMod H.realizesFiniteNontrivial.p]
      H.presentedAugmentationQuotient (rels := rels) hrels (n - 1)

/--
The canonical generator-side family, obtained by left multiplication by the
generator differences `of(j) - 1`.
-/
noncomputable def PPDatum.pres_augcanon_gencomponents
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) :
    H.pres_aug_gencomponents hrels n := by
  intro j
  exact
    H.pres_augquot_leftmul
      (hrels := hrels) (n := n) (m := n - 1) (Nat.sub_le _ _)
      (H.pres_aug_gendifference j)

/--
The type of the relator-side component maps in the eventual
Golod--Shafarevich linear map.
-/
abbrev PPDatum.pres_aug_relatorcompone
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ) :=
  ∀ i : PPDatum.activeRelators H depth n,
    H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1) →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n

/--
Relator-side correction data given by explicit coefficients in the presented
group algebra, one coefficient for each active relator and generator.

The intended next step is to choose these coefficients inside the augmentation
power `I^(depth i - 1)` coming from the depth of the corresponding relator.
-/
structure PPDatum.PresAugRelatorcoeffs
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (n : ℕ) where
  coeff :
    ∀ _ : PPDatum.activeRelators H depth n, Fin H.generatorRank →
      MonoidAlgebra (ZMod H.realizesFiniteNontrivial.p)
        (PresentedGroup (Set.range rels))
  mem_pow' :
    ∀ i j,
      coeff i j ∈
        GShafar.augmentationIdeal
          (R := ZMod H.realizesFiniteNontrivial.p)
          (G := PresentedGroup (Set.range rels)) ^ (depth i.1 - 1)

/--
Explicit relator coefficients in `I^(depth i - 1)` determine concrete
relator-side component maps by left multiplication on the corresponding deeper
augmentation quotient.
-/
noncomputable def PPDatum.pres_augcanon_relatorcompone
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (hdepth1 : ∀ i : PPDatum.activeRelators H depth n, 1 ≤ depth i.1)
    (Ψ :
      H.PresAugRelatorcoeffs
        (rels := rels) (depth := depth) n) :
    H.pres_aug_relatorcompone (depth := depth) hrels n := by
  intro i
  refine LinearMap.pi ?_
  intro j
  have hi_le : depth i.1 ≤ n := i.2
  have hi_pos : 1 ≤ depth i.1 := hdepth1 i
  have hshift : (n - depth i.1) + (depth i.1 - 1) = n - 1 := by
    omega
  have hshift2 :
      n - depth i.1 + (depth i.1 - 1) + 2 = (n - 1) + 2 := by
    omega
  let g :=
    H.presaug_quotleft_mulmempow
      (hrels := hrels)
      (n := n - depth i.1)
      (k := depth i.1 - 1)
      (a := Ψ.coeff i j)
      (ha := Ψ.mem_pow' i j)
  have g' :
      H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1) →ₗ[ZMod
        H.realizesFiniteNontrivial.p]
        H.presentedAugmentationQuotient (rels := rels) hrels (n - 1) := by
    let B :=
      MonoidAlgebra (ZMod H.realizesFiniteNontrivial.p) (PresentedGroup (Set.range rels))
    let J : Ideal B :=
      GShafar.augmentationIdeal
        (R := ZMod H.realizesFiniteNontrivial.p) (G := PresentedGroup (Set.range rels))
    have hJ :
        J ^ (n - depth i.1 + (depth i.1 - 1) + 2) = J ^ (n - 1 + 2) := by
      exact congrArg (fun m => J ^ m) hshift2
    let e :=
      Ideal.quotientEquivAlgOfEq (R₁ := ZMod H.realizesFiniteNontrivial.p) (A := B) hJ
    simpa [PPDatum.presentedAugmentationQuotient, B, J] using
      e.toLinearMap.comp g
  exact g'

/--
Assemble the generator-side component family into a single map from the
principal augmentation quotient to the active target.
-/
noncomputable def PPDatum.pres_aug_genmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (Γ : H.pres_aug_gencomponents hrels n) :
    H.presentedAugmentationQuotient (rels := rels) hrels n →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n :=
  LinearMap.pi Γ

/--
Assemble the relator-side component family into a single map from the active
relator quotient factors to the active target.
-/
noncomputable def PPDatum.pres_aug_relatormap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (Φ : H.pres_aug_relatorcompone (depth := depth) hrels n) :
    (∀ i : PPDatum.activeRelators H depth n,
        H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1)) →ₗ[ZMod
          H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n := by
  classical
  refine
    { toFun := fun z => ∑ i, Φ i (z i)
      map_add' := by
        intro z w
        ext j
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c z
        ext j
        simp [Finset.smul_sum] }

/--
The abstract Golod--Shafarevich map obtained by combining the generator-side
and relator-side component families.
-/
noncomputable def PPDatum.pres_aug_assembledmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (Γ : H.pres_aug_gencomponents hrels n)
    (Φ : H.pres_aug_relatorcompone (depth := depth) hrels n) :
    H.pres_aug_activesource (rels := rels) hrels depth n →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n :=
  (H.pres_aug_genmap hrels n Γ).comp
      (LinearMap.fst (ZMod H.realizesFiniteNontrivial.p)
        (H.presentedAugmentationQuotient (rels := rels) hrels n)
        (∀ i : PPDatum.activeRelators H depth n,
          H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1))) +
    (H.pres_aug_relatormap hrels n Φ).comp
      (LinearMap.snd (ZMod H.realizesFiniteNontrivial.p)
        (H.presentedAugmentationQuotient (rels := rels) hrels n)
        (∀ i : PPDatum.activeRelators H depth n,
          H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1)))

/--
The assembled map with the generator-side family fixed to the canonical
multiplication maps by `of(j) - 1`.
-/
noncomputable def PPDatum.pres_augcanon_assembledmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (Φ : H.pres_aug_relatorcompone (depth := depth) hrels n) :
    H.pres_aug_activesource (rels := rels) hrels depth n →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n :=
  H.pres_aug_assembledmap hrels n
    (H.pres_augcanon_gencomponents hrels n) Φ

/--
The fully named canonical Golod--Shafarevich map built from the generator
differences `of(j) - 1` together with an explicit relator coefficient package.
-/
noncomputable def PPDatum.pres_aug_canonmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (hdepth1 : ∀ i : PPDatum.activeRelators H depth n, 1 ≤ depth i.1)
    (Ψ :
      H.PresAugRelatorcoeffs
        (rels := rels) (depth := depth) n) :
    H.pres_aug_activesource (rels := rels) hrels depth n →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n :=
  H.pres_augcanon_assembledmap hrels n
    (H.pres_augcanon_relatorcompone hrels n hdepth1 Ψ)

/-
The remaining Hilbert-series frontier is now a concrete linear-algebra problem
on named quotient spaces: construct a surjective linear map from the active
presented augmentation source to the corresponding target.
-/
theorem
    PPDatum.finrankpres_augactivetarget_lesourcesurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (f :
      H.pres_aug_activesource (rels := rels) hrels depth n →ₗ[ZMod
        H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n)
    (hf : Function.Surjective f) :
    Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (H.pres_aug_activetarget (rels := rels) hrels n) ≤
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (H.pres_aug_activesource (rels := rels) hrels depth n) := by
  exact
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_surjective f hf)
      (Module.rank_lt_aleph0 (ZMod H.realizesFiniteNontrivial.p)
        (H.pres_aug_activesource (rels := rels) hrels depth n))

/-
Surjectivity of the assembled Golod--Shafarevich map implies the corresponding
dimension inequality between the concrete active target and source spaces.
-/
set_option linter.style.longLine false in
theorem
    PPDatum.finrankpres_augactive_assemapsurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (Γ : H.pres_aug_gencomponents hrels n)
    (Φ : H.pres_aug_relatorcompone (depth := depth) hrels n)
    (hf : Function.Surjective (H.pres_aug_assembledmap hrels n Γ Φ)) :
    Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (H.pres_aug_activetarget (rels := rels) hrels n) ≤
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (H.pres_aug_activesource (rels := rels) hrels depth n) := by
  exact
    H.finrankpres_augactivetarget_lesourcesurj
      hrels n (H.pres_aug_assembledmap hrels n Γ Φ) hf

/--
Once the relator-side correction maps are chosen, surjectivity of the assembled
map with the canonical generator factors already implies the exact concrete
coefficient inequality for the active augmentation quotients.
-/
theorem
    PPDatum.presaug_dimineq_assemapsurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (Φ : H.pres_aug_relatorcompone (depth := depth) hrels n)
    (hf : Function.Surjective (H.pres_augcanon_assembledmap hrels n Φ)) :
    H.generatorRank *
        H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) ≤
      H.pres_aug_quotfinrank (rels := rels) hrels n +
        ∑ i, if depth i ≤ n then
          H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)
        else 0 := by
  letI (k : ℕ) :
      Module.Free (ZMod H.realizesFiniteNontrivial.p)
        (H.presentedAugmentationQuotient (rels := rels) hrels k) := by
    infer_instance
  have hsum_active :
      (∑ x : PPDatum.activeRelators H depth n,
          H.pres_aug_quotfinrank (rels := rels) hrels (n - depth x.1)) =
        ∑ i, if depth i ≤ n then
          H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)
        else 0 := by
    simpa using
      (H.sum_active_relatorseq depth n
        (fun i => H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)))
  have hle :=
    H.finrankpres_augactive_assemapsurj
      hrels n (H.pres_augcanon_gencomponents hrels n) Φ hf
  have htarget0 :
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
          (Fin H.generatorRank →
            H.presentedAugmentationQuotient (rels := rels) hrels (n - 1)) =
        H.generatorRank *
          H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) := by
    simp [H.finrank_pres_augquot, Module.finrank_pi_fintype]
  have htarget :
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
          (H.pres_aug_activetarget (rels := rels) hrels n) =
        H.generatorRank *
          H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) := by
    simpa [PPDatum.pres_aug_activetarget] using htarget0
  have hsource0 :
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
          ((H.presentedAugmentationQuotient (rels := rels) hrels n) ×
            ((i : PPDatum.activeRelators H depth n) →
              H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1))) =
        H.pres_aug_quotfinrank (rels := rels) hrels n +
          ∑ x : PPDatum.activeRelators H depth n,
            H.pres_aug_quotfinrank (rels := rels) hrels (n - depth x.1) := by
    simp [H.finrank_pres_augquot, Module.finrank_prod,
      Module.finrank_pi_fintype]
  change
    Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (Fin H.generatorRank →
          H.presentedAugmentationQuotient (rels := rels) hrels (n - 1)) ≤
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        ((H.presentedAugmentationQuotient (rels := rels) hrels n) ×
          ((i : PPDatum.activeRelators H depth n) →
            H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1))) at hle
  rw [htarget0, hsource0, hsum_active] at hle
  exact hle

/--
Surjectivity of the fully named canonical map attached to a relator
coefficient package implies the concrete quotient-dimension inequality needed
at step `n`.
-/
theorem
    PPDatum.presaug_dimineq_canonmapsurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (hdepth1 : ∀ i : PPDatum.activeRelators H depth n, 1 ≤ depth i.1)
    (Ψ :
      H.PresAugRelatorcoeffs
        (rels := rels) (depth := depth) n)
    (hf : Function.Surjective (H.pres_aug_canonmap hrels n hdepth1 Ψ)) :
    H.generatorRank *
        H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) ≤
      H.pres_aug_quotfinrank (rels := rels) hrels n +
        ∑ i, if depth i ≤ n then
          H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)
        else 0 := by
  exact
    H.presaug_dimineq_assemapsurj
      hrels n
      (H.pres_augcanon_relatorcompone hrels n hdepth1 Ψ) hf

/--
Depth bounds `2 ≤ depth i` automa give the positivity condition needed to
form the canonical map at each active index.
-/
theorem PPDatum.one_ledepth_activerelator
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ}
    {n : ℕ}
    (hdepth : ∀ i, 2 ≤ depth i) :
    ∀ i : PPDatum.activeRelators H depth n, 1 ≤ depth i.1 := by
  intro i
  exact le_trans (by decide : 1 ≤ 2) (hdepth i.1)

/--
To prove the finite-window quotient-dimension inequalities, it is enough to
show that at each relevant index `n` some concrete relator coefficient package
makes the named canonical Golod--Shafarevich map surjective.
-/
theorem
    PPDatum.presaug_windowdimineq_canonmapsurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hdepth : ∀ i, 2 ≤ depth i)
    {N : ℕ}
    (hsurj :
      ∀ n ≤ N + max 1 (Finset.univ.sup depth),
        ∃ Ψ :
          H.PresAugRelatorcoeffs
            (rels := rels) (depth := depth) n,
          Function.Surjective
            (H.pres_aug_canonmap hrels n
              (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth) Ψ)) :
    ∀ n ≤ N + max 1 (Finset.univ.sup depth),
      H.generatorRank *
          H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) ≤
        H.pres_aug_quotfinrank (rels := rels) hrels n +
          ∑ i, if depth i ≤ n then
            H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)
          else 0 := by
  intro n hn
  rcases hsurj n hn with ⟨Ψ, hΨ⟩
  exact
    H.presaug_dimineq_canonmapsurj
      hrels n
      (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth) Ψ hΨ

/--
If the relator-side map alone is already surjective, then the generator term
disappears and one gets the sharp boundary inequality needed at the truncation
step `n = N + 1`.
-/
theorem
    PPDatum.presaug_bounddimineq_relatormapsurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (n : ℕ)
    (Φ : H.pres_aug_relatorcompone (depth := depth) hrels n)
    (hf : Function.Surjective (H.pres_aug_relatormap hrels n Φ)) :
    H.generatorRank *
        H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) ≤
      ∑ i, if depth i ≤ n then
        H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)
      else 0 := by
  letI (k : ℕ) :
      Module.Free (ZMod H.realizesFiniteNontrivial.p)
        (H.presentedAugmentationQuotient (rels := rels) hrels k) := by
    infer_instance
  have hsum_active :
      (∑ x : PPDatum.activeRelators H depth n,
          H.pres_aug_quotfinrank (rels := rels) hrels (n - depth x.1)) =
        ∑ i, if depth i ≤ n then
          H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)
        else 0 := by
    simpa using
      (H.sum_active_relatorseq depth n
        (fun i => H.pres_aug_quotfinrank (rels := rels) hrels (n - depth i)))
  have hle :=
    Module.finrank_le_finrank_of_rank_le_rank
      (LinearMap.lift_rank_le_of_surjective
        (H.pres_aug_relatormap hrels n Φ) hf)
      (Module.rank_lt_aleph0 (ZMod H.realizesFiniteNontrivial.p)
        ((i : PPDatum.activeRelators H depth n) →
          H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1)))
  have htarget0 :
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
          (Fin H.generatorRank →
            H.presentedAugmentationQuotient (rels := rels) hrels (n - 1)) =
        H.generatorRank *
          H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) := by
    simp [H.finrank_pres_augquot, Module.finrank_pi_fintype]
  have hsource0 :
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
          ((i : PPDatum.activeRelators H depth n) →
            H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1)) =
        ∑ x : PPDatum.activeRelators H depth n,
          H.pres_aug_quotfinrank (rels := rels) hrels (n - depth x.1) := by
    simp [H.finrank_pres_augquot, Module.finrank_pi_fintype]
  change
    Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        (Fin H.generatorRank →
          H.presentedAugmentationQuotient (rels := rels) hrels (n - 1)) ≤
      Module.finrank (ZMod H.realizesFiniteNontrivial.p)
        ((i : PPDatum.activeRelators H depth n) →
          H.presentedAugmentationQuotient (rels := rels) hrels (n - depth i.1)) at hle
  rw [htarget0, hsource0, hsum_active] at hle
  exact hle

/-
To pass from the untruncated quotient-dimension inequalities to the earlier
finite-window Hilbert-series bridge, it suffices to know those inequalities for
the positive indices `n ≤ N` together with the single boundary inequality at
`n = N + 1`.

For `n = 0` the truncation inequality is automatic, and for `n ≥ N + 2` it is
trivial because the truncated generator term has already vanished.
-/
set_option linter.style.longLine false in
theorem
    PPDatum.minpres_hilbseriaug_windowdimineq
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            (∀ n, 1 ≤ n → n ≤ N →
              H.generatorRank *
                  H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) ≤
                H.pres_aug_quotfinrank (rels := rels) hrels n +
                  ∑ i, if depth i ≤ n then
                    H.pres_aug_quotfinrank
                      (rels := rels) hrels (n - depth i)
                  else 0) ∧
              H.generatorRank *
                  H.pres_aug_quotfinrank (rels := rels) hrels N ≤
                ∑ i, if depth i ≤ N + 1 then
                  H.pres_aug_quotfinrank
                    (rels := rels) hrels (N + 1 - depth i)
                else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine
    H.minpres_hilbserifin_windowdimineq
      ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hmain, hboundary⟩
  refine ⟨N, ?_⟩
  intro n hn
  by_cases h0 : n = 0
  · subst h0
    simp
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero h0)
  by_cases hnN : n ≤ N
  · have hmain' := hmain n hn1 hnN
    have hnm1 : n - 1 ≤ N := le_trans (Nat.sub_le _ _) hnN
    have hsum :
        (∑ i, if depth i ≤ n then
            if n ≤ N + depth i then
              H.pres_aug_quotfinrank
                (rels := rels) hrels (n - depth i)
            else 0
          else 0) =
          ∑ i, if depth i ≤ n then
            H.pres_aug_quotfinrank
              (rels := rels) hrels (n - depth i)
          else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hdi : depth i ≤ n
      · have hsub : n ≤ N + depth i := le_trans hnN (Nat.le_add_right _ _)
        simp [hdi, hsub]
      · simp [hdi]
    have hleft :
        H.generatorRank * (if 1 ≤ n then
            if n - 1 ≤ N then
              H.pres_aug_quotfinrank (rels := rels) hrels (n - 1)
            else 0
          else 0) =
          H.generatorRank *
            H.pres_aug_quotfinrank (rels := rels) hrels (n - 1) := by
      simp [hn1, hnm1]
    have hright :
        ((if n ≤ N then
            H.pres_aug_quotfinrank (rels := rels) hrels n
          else 0) +
            ∑ i, if depth i ≤ n then
              if n - depth i ≤ N then
                H.pres_aug_quotfinrank
                  (rels := rels) hrels (n - depth i)
              else 0
            else 0) =
          (H.pres_aug_quotfinrank (rels := rels) hrels n +
            ∑ i, if depth i ≤ n then
              H.pres_aug_quotfinrank
                (rels := rels) hrels (n - depth i)
            else 0) := by
      simp [hnN, hsum]
    rw [hleft, hright]
    exact hmain'
  · have hsplit : n = N + 1 ∨ N + 2 ≤ n := by
      omega
    cases hsplit with
    | inl hsucc =>
        subst hsucc
        have hsum :
            (∑ i, if depth i ≤ N + 1 then
                if 1 ≤ depth i then
                  H.pres_aug_quotfinrank
                    (rels := rels) hrels (N + 1 - depth i)
                else 0
              else 0) =
              ∑ i, if depth i ≤ N + 1 then
                H.pres_aug_quotfinrank
                  (rels := rels) hrels (N + 1 - depth i)
              else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hdi : depth i ≤ N + 1
          · have hpos : 1 ≤ depth i := le_trans (by decide : 1 ≤ 2) (hdepth i)
            simp [hdi, hpos]
          · simp [hdi]
        have hleft :
            H.generatorRank * (if 1 ≤ N + 1 then
                if N + 1 - 1 ≤ N then
                  H.pres_aug_quotfinrank (rels := rels) hrels (N + 1 - 1)
                else 0
              else 0) =
              H.generatorRank *
                H.pres_aug_quotfinrank (rels := rels) hrels N := by
          simp
        have hright :
            ((if N + 1 ≤ N then
                H.pres_aug_quotfinrank (rels := rels) hrels (N + 1)
              else 0) +
                ∑ i, if depth i ≤ N + 1 then
                  if N + 1 - depth i ≤ N then
                    H.pres_aug_quotfinrank
                      (rels := rels) hrels (N + 1 - depth i)
                  else 0
                else 0) =
              (∑ i, if depth i ≤ N + 1 then
                H.pres_aug_quotfinrank
                  (rels := rels) hrels (N + 1 - depth i)
              else 0) := by
          simp [hsum]
        rw [hleft, hright]
        exact hboundary
    | inr hbig =>
        have hnm1 : ¬ n - 1 ≤ N := by
          omega
        have hleft :
            H.generatorRank * (if 1 ≤ n then
                if n - 1 ≤ N then
                  H.pres_aug_quotfinrank (rels := rels) hrels (n - 1)
                else 0
              else 0) = 0 := by
          simp [hn1, hnm1]
        have hright :
            ((if n ≤ N then
                H.pres_aug_quotfinrank (rels := rels) hrels n
              else 0) +
                ∑ i, if depth i ≤ n then
                  if n - depth i ≤ N then
                    H.pres_aug_quotfinrank
                      (rels := rels) hrels (n - depth i)
                  else 0
                else 0) =
              (∑ i, if depth i ≤ n then
                if n - depth i ≤ N then
                  H.pres_aug_quotfinrank
                    (rels := rels) hrels (n - depth i)
                else 0
              else 0) := by
          simp [hnN]
        rw [hleft, hright]
        exact Nat.zero_le _

/-
The Hilbert-series bridge now reduces to two explicit finite tasks:
construct canonical-map surjections for the positive indices `n ≤ N`, and
separately discharge the single boundary inequality at `n = N + 1`.
-/
set_option linter.style.longLine false in
theorem
    PPDatum.minpres_hilbertseries_surjupbound
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            (∀ n, 1 ≤ n → n ≤ N →
              ∃ Ψ :
                H.PresAugRelatorcoeffs
                  (rels := rels) (depth := depth) n,
                Function.Surjective
                  (H.pres_aug_canonmap hrels n
                    (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth) Ψ)) ∧
              H.generatorRank *
                  H.pres_aug_quotfinrank (rels := rels) hrels N ≤
                ∑ i, if depth i ≤ N + 1 then
                  H.pres_aug_quotfinrank
                    (rels := rels) hrels (N + 1 - depth i)
                else 0) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine
    H.minpres_hilbseriaug_windowdimineq
      ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hsurj, hboundary⟩
  refine ⟨N, ?_, hboundary⟩
  intro n hn1 hnN
  rcases hsurj n hn1 hnN with ⟨Ψ, hΨ⟩
  exact
    H.presaug_dimineq_canonmapsurj
      hrels n
      (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth) Ψ hΨ

/-
The single boundary inequality at `n = N + 1` can itself be supplied by a
surjective relator-only map, leaving the remaining work as explicit
surjectivity constructions on named quotient spaces.
-/
set_option linter.style.longLine false in
theorem
    PPDatum.minpres_hilbertseries_relabounsurj
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ N : ℕ,
            (∀ n, 1 ≤ n → n ≤ N →
              ∃ Ψ :
                H.PresAugRelatorcoeffs
                  (rels := rels) (depth := depth) n,
                Function.Surjective
                  (H.pres_aug_canonmap hrels n
                    (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth) Ψ)) ∧
              ∃ Φ : H.pres_aug_relatorcompone (depth := depth) hrels (N + 1),
                Function.Surjective (H.pres_aug_relatormap hrels (N + 1) Φ)) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine
    H.minpres_hilbertseries_surjupbound
      ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨N, hsurj, Φ, hΦ⟩
  refine ⟨N, hsurj, ?_⟩
  exact
    H.presaug_bounddimineq_relatormapsurj
      hrels (N + 1) Φ hΦ

/--
A canonical finite cutoff for the remaining Golod--Shafarevich surjectivity
tasks: the maximal declared relator depth.
-/
abbrev PPDatum.pres_aug_canonwindow
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} : ℕ :=
  Finset.univ.sup depth

/--
The single boundary index immediately after the canonical depth window.
-/
abbrev PPDatum.pres_aug_canonbound
    (H : PPDatum)
    {depth : Fin H.relationRank → ℕ} : ℕ :=
  H.pres_aug_canonwindow (depth := depth) + 1

/--
A choice of relator coefficient packages on the canonical window
`1 ≤ n ≤ sup depth`, together with surjectivity of the resulting canonical
Golod--Shafarevich maps.
-/
structure PPDatum.PresAugcanonWindowwitness
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hdepth : ∀ i, 2 ≤ depth i) where
  coeff :
    ∀ n, 1 ≤ n → n ≤ H.pres_aug_canonwindow (depth := depth) →
      H.PresAugRelatorcoeffs (rels := rels) (depth := depth) n
  surj :
    ∀ n hn1 hnN,
      Function.Surjective
        (H.pres_aug_canonmap hrels n
          (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth)
          (coeff n hn1 hnN))

/--
A relator-only boundary map at the canonical boundary index together with its
surjectivity proof.
-/
structure PPDatum.PresAugcanonBoundwitness
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    where
  components :
    H.pres_aug_relatorcompone (depth := depth) hrels
      (H.pres_aug_canonbound (depth := depth))
  surj :
    Function.Surjective
      (H.pres_aug_relatormap hrels
        (H.pres_aug_canonbound (depth := depth)) components)

/--
Canonical relator coefficient data on the window `1 ≤ n ≤ sup depth`.

This packages only the explicit coefficient choices; surjectivity of the
resulting named maps is recorded separately.
-/
structure PPDatum.PresAugcanonWindowdata
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ} where
  coeff :
    ∀ n, 1 ≤ n → n ≤ H.pres_aug_canonwindow (depth := depth) →
      H.PresAugRelatorcoeffs (rels := rels) (depth := depth) n

/--
Canonical relator-side component data at the single boundary index
`sup depth + 1`.
-/
abbrev PPDatum.pres_augcanon_bounddata
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) :=
  H.pres_aug_relatorcompone (depth := depth) hrels
    (H.pres_aug_canonbound (depth := depth))

/--
The specifically named canonical map on the depth window obtained from a fixed
coefficient family.
-/
noncomputable def PPDatum.pres_augcanon_windowmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hdepth : ∀ i, 2 ≤ depth i)
    (window :
      H.PresAugcanonWindowdata
        (rels := rels) (depth := depth))
    (n : ℕ)
    (hn1 : 1 ≤ n)
    (hnN : n ≤ H.pres_aug_canonwindow (depth := depth)) :
    H.pres_aug_activesource (rels := rels) hrels depth n →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n :=
  H.pres_aug_canonmap hrels n
    (H.one_ledepth_activerelator (depth := depth) (n := n) hdepth)
    (window.coeff n hn1 hnN)

/--
The specifically named boundary relator map obtained from fixed relator-side
components at `sup depth + 1`.
-/
noncomputable def PPDatum.pres_augcanon_boundmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (boundary :
      H.pres_augcanon_bounddata
        (rels := rels) (depth := depth) hrels) :
    (∀ i : PPDatum.activeRelators H depth
        (H.pres_aug_canonbound (depth := depth)),
        H.presentedAugmentationQuotient (rels := rels) hrels
          (H.pres_aug_canonbound (depth := depth) - depth i.1)) →ₗ[ZMod
            H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels
        (H.pres_aug_canonbound (depth := depth)) :=
  H.pres_aug_relatormap hrels
    (H.pres_aug_canonbound (depth := depth)) boundary

/--
Canonical candidate data for the remaining Golod--Shafarevich surjectivity
tasks: window coefficient choices together with a boundary relator family.
-/
structure PPDatum.PresAugCanondata
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    where
  window :
    H.PresAugcanonWindowdata
      (rels := rels) (depth := depth)
  boundary :
    H.pres_augcanon_bounddata
      (rels := rels) (depth := depth) hrels

/--
The zero relator coefficient package at step `n`.
-/
def PPDatum.pres_augzero_relatorcoeffs
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (n : ℕ) :
    H.PresAugRelatorcoeffs
      (rels := rels) (depth := depth) n where
  coeff _ _ := 0
  mem_pow' _ _ := Ideal.zero_mem _

/--
The canonical window data obtained by taking the zero coefficient package at
every index `1 ≤ n ≤ sup depth`.
-/
def PPDatum.presaug_zerocanon_windowdata
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ} :
    H.PresAugcanonWindowdata
      (rels := rels) (depth := depth) where
  coeff n _ _ :=
    H.pres_augzero_relatorcoeffs
      (rels := rels) (depth := depth) n

/--
The canonical boundary data obtained by taking every relator-side component to
be the zero map.
-/
noncomputable def PPDatum.presaug_zerocanon_bounddata
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) :
    H.pres_augcanon_bounddata
      (rels := rels) (depth := depth) hrels := by
  intro i
  exact 0

/--
The specifically named canonical candidate data obtained by taking zero
relator coefficients on the window and the zero relator-side family at the
boundary.
-/
noncomputable def PPDatum.pres_augzero_canondata
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) :
    H.PresAugCanondata
      (rels := rels) (depth := depth) hrels where
  window :=
    H.presaug_zerocanon_windowdata
      (rels := rels) (depth := depth)
  boundary :=
    H.presaug_zerocanon_bounddata
      (rels := rels) (depth := depth) hrels

/--
The named canonical window map attached to the zero coefficient data.
-/
noncomputable def PPDatum.presaug_zerocanon_windowmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hdepth : ∀ i, 2 ≤ depth i)
    (n : ℕ)
    (hn1 : 1 ≤ n)
    (hnN : n ≤ H.pres_aug_canonwindow (depth := depth)) :
    H.pres_aug_activesource (rels := rels) hrels depth n →ₗ[ZMod
      H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels n :=
  H.pres_augcanon_windowmap hrels hdepth
    (H.presaug_zerocanon_windowdata
      (rels := rels) (depth := depth))
    n hn1 hnN

/--
The named canonical boundary map attached to the zero boundary data.
-/
noncomputable def PPDatum.presaug_zerocanon_boundmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) :
    (∀ i : PPDatum.activeRelators H depth
        (H.pres_aug_canonbound (depth := depth)),
        H.presentedAugmentationQuotient (rels := rels) hrels
          (H.pres_aug_canonbound (depth := depth) - depth i.1)) →ₗ[ZMod
            H.realizesFiniteNontrivial.p]
      H.pres_aug_activetarget (rels := rels) hrels
        (H.pres_aug_canonbound (depth := depth)) :=
  H.pres_augcanon_boundmap hrels
    (H.presaug_zerocanon_bounddata
      (rels := rels) (depth := depth) hrels)

/--
The zero canonical boundary map is definitionally the zero linear map, so it is
not a plausible source of the final surjectivity witness except in degenerate
cases where the target already vanishes.
-/
theorem PPDatum.presaug_zerocanonbound_mapeqzero
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) :
    H.presaug_zerocanon_boundmap
        (rels := rels) (depth := depth) hrels =
      0 := by
  classical
  apply LinearMap.ext
  intro z
  funext j
  unfold PPDatum.presaug_zerocanon_boundmap
  unfold PPDatum.pres_augcanon_boundmap
  unfold PPDatum.pres_aug_relatormap
  dsimp [PPDatum.presaug_zerocanon_bounddata]
  simp

/--
Surjectivity of the named canonical window maps attached to fixed coefficient
data produces the packaged canonical window witness.
-/
def PPDatum.presaug_canonwindow_witnesssurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hdepth : ∀ i, 2 ≤ depth i)
    (window :
      H.PresAugcanonWindowdata
        (rels := rels) (depth := depth))
    (hsurj :
      ∀ n hn1 hnN,
        Function.Surjective
          (H.pres_augcanon_windowmap hrels hdepth window n hn1 hnN)) :
    H.PresAugcanonWindowwitness
      (rels := rels) (depth := depth) hrels hdepth := by
  refine ⟨window.coeff, ?_⟩
  intro n hn1 hnN
  exact hsurj n hn1 hnN

/--
Surjectivity of the named canonical boundary relator map produces the packaged
boundary witness.
-/
def PPDatum.presaug_canonbound_witnesssurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (boundary :
      H.pres_augcanon_bounddata
        (rels := rels) (depth := depth) hrels)
    (hsurj :
      Function.Surjective
        (H.pres_augcanon_boundmap hrels boundary)) :
    H.PresAugcanonBoundwitness
      (rels := rels) (depth := depth) hrels := by
  refine ⟨boundary, ?_⟩
  simpa [PPDatum.pres_augcanon_boundmap] using hsurj

/--
If fixed canonical coefficient and boundary data make the corresponding named
maps surjective, then the remaining bridge inputs are already fully packaged.
-/
def PPDatum.pres_augcanon_witnessessurj
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hdepth : ∀ i, 2 ≤ depth i)
    (data :
      H.PresAugCanondata
        (rels := rels) (depth := depth) hrels)
    (hwindow :
      ∀ n hn1 hnN,
        Function.Surjective
          (H.pres_augcanon_windowmap
            hrels hdepth data.window n hn1 hnN))
    (hboundary :
      Function.Surjective
        (H.pres_augcanon_boundmap hrels data.boundary)) :
    H.PresAugcanonWindowwitness
        (rels := rels) (depth := depth) hrels hdepth ×
      H.PresAugcanonBoundwitness
        (rels := rels) (depth := depth) hrels := by
  refine ⟨?_, ?_⟩
  · exact
      H.presaug_canonwindow_witnesssurj
        hrels hdepth data.window hwindow
  · exact
      H.presaug_canonbound_witnesssurj
        hrels data.boundary hboundary

/-
The final Hilbert-series bridge can now be expressed using a fixed canonical
window `1 ≤ n ≤ sup depth` and the single canonical boundary index
`sup depth + 1`.
-/
set_option linter.style.longLine false in
theorem
    PPDatum.minpres_hilbseribrid_canowindwitn
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          H.PresAugcanonWindowwitness
              (rels := rels) (depth := depth) hrels hdepth ×
            H.PresAugcanonBoundwitness
              (rels := rels) (depth := depth) hrels) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine
    H.minpres_hilbertseries_relabounsurj
      ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨window, boundary⟩
  refine ⟨H.pres_aug_canonwindow (depth := depth), ?_, ?_⟩
  · intro n hn1 hnN
    exact ⟨window.coeff n hn1 hnN, window.surj n hn1 hnN⟩
  · refine ⟨boundary.components, ?_⟩
    simpa [PPDatum.pres_aug_canonbound] using
      boundary.surj

/--
The final Hilbert-series bridge can be reduced all the way to surjectivity of
specifically named canonical window and boundary maps attached to fixed
candidate data.
-/
theorem
    PPDatum.minpres_hilbseribrid_canondatasurj
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ data :
              H.PresAugCanondata
                (rels := rels) (depth := depth) hrels,
            (∀ n hn1 hnN,
              Function.Surjective
                (H.pres_augcanon_windowmap
                  hrels hdepth data.window n hn1 hnN)) ∧
              Function.Surjective
                (H.pres_augcanon_boundmap hrels data.boundary)) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  classical
  refine H.minpres_hilbseribrid_canowindwitn ?_
  intro rels depth hrels hmem hdepth
  let data := Classical.choose (hwitness hrels hmem hdepth)
  have hdata := Classical.choose_spec (hwitness hrels hmem hdepth)
  exact
    H.pres_augcanon_witnessessurj
      hrels hdepth data hdata.1 hdata.2

/--
An honest name for the remaining finite-dimensional input: choose explicit
presented-side bridge data and prove surjectivity of the corresponding named
window and boundary maps.
-/
abbrev PPDatum.PresAugBridgedata
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) :=
  H.PresAugCanondata (rels := rels) (depth := depth) hrels

/--
The named window map attached to a chosen bridge data package.
-/
abbrev PPDatum.pres_augbridge_windowmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (hdepth : ∀ i, 2 ≤ depth i)
    (data :
      H.PresAugBridgedata
        (rels := rels) (depth := depth) hrels)
    (n : ℕ)
    (hn1 : 1 ≤ n)
    (hnN : n ≤ H.pres_aug_canonwindow (depth := depth)) :=
  H.pres_augcanon_windowmap hrels hdepth data.window n hn1 hnN

/--
The named boundary map attached to a chosen bridge data package.
-/
abbrev PPDatum.pres_augbridge_boundmap
    (H : PPDatum)
    {rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)}
    {depth : Fin H.relationRank → ℕ}
    (hrels : Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier))
    (data :
      H.PresAugBridgedata
        (rels := rels) (depth := depth) hrels) :=
  H.pres_augcanon_boundmap hrels data.boundary

/--
The remaining Hilbert-series bridge reduces to surjectivity of the named maps
attached to an explicit bridge-data package.
-/
theorem
    PPDatum.minpres_hilbseribrid_bridgedatasurj
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
          ∃ data :
              H.PresAugBridgedata
                (rels := rels) (depth := depth) hrels,
            (∀ n hn1 hnN,
              Function.Surjective
                (H.pres_augbridge_windowmap
                  (rels := rels) (depth := depth) hrels hdepth data n hn1 hnN)) ∧
              Function.Surjective
                (H.pres_augbridge_boundmap
                  (rels := rels) (depth := depth) hrels data)) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine H.minpres_hilbseribrid_canondatasurj ?_
  intro rels depth hrels hmem hdepth
  rcases hwitness hrels hmem hdepth with ⟨data, hwindow, hboundary⟩
  exact ⟨data, hwindow, hboundary⟩

/--
As a degenerate placeholder, even surjectivity of the zero-data maps would
imply the Hilbert-series bridge, but the boundary map above shows that this is
not the right general frontier.
-/
theorem
    PPDatum.minpreshilbert_seribridzero_canondatasurj
    (H : PPDatum)
    (hwitness :
      ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
        ⦃depth : Fin H.relationRank → ℕ⦄,
          (hrels :
            Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier)) →
          (hmem : ∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
          (hdepth : ∀ i, 2 ≤ depth i) →
            (∀ n hn1 hnN,
              Function.Surjective
                (H.presaug_zerocanon_windowmap
                  (rels := rels) (depth := depth) hrels hdepth n hn1 hnN)) ∧
              Function.Surjective
                (H.presaug_zerocanon_boundmap
                  (rels := rels) (depth := depth) hrels)) :
    ∀ ⦃rels : Fin H.relationRank → FreeGroup (Fin H.generatorRank)⦄
      ⦃depth : Fin H.relationRank → ℕ⦄,
        Nonempty (PresentedGroup (Set.range rels) ≃* H.realizesFiniteNontrivial.carrier) →
        (∀ i, rels i ∈ H.relatorZassenhausFiltration (depth i)) →
        (∀ i, 2 ≤ depth i) →
        ∀ t : ℝ, 0 < t → t < 1 →
          0 < GShafar.relatorExpression H.generatorRank H.relationRank depth t := by
  refine H.minpres_hilbseribrid_canondatasurj ?_
  intro rels depth hrels hmem hdepth
  refine
    ⟨H.pres_augzero_canondata
      (rels := rels) (depth := depth) hrels, ?_⟩
  simpa
    [PPDatum.pres_augzero_canondata,
      PPDatum.presaug_zerocanon_windowmap,
      PPDatum.presaug_zerocanon_boundmap]
    using hwitness hrels hmem hdepth


theorem golod_shafarevich_pro
    (H : PPDatum)
    (hseries : H.PRSeries) :
    (H.relationRank : ℝ) > (H.generatorRank : ℝ) ^ (2 : ℕ) / 4 := by
  apply golod_shafarevich_bounds
  exact GShafar.pos_positive_witness hseries

end Towers
