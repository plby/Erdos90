import Mathlib
import Towers.Algebra.CompletedGroupAlgebra.AmbientConstruction
import Towers.Algebra.DenseGenerators.CoreJennings


open scoped Topology Pointwise BigOperators

noncomputable section

namespace Towers

universe u
universe v w z

/-- Density of canonical units upstairs descends to density in the augmentation quotient. -/
lemma DCCore.densecanon_unitquot_spanalgspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hdense : M.DenseAlgebraSpan) :
    M.DenseCanonunitQuotspan := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instUniformSpace
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  let algebraSpan : Submodule (ZMod p) M.completedGroupAlgebra :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ => (M.canonicalUnit g : M.completedGroupAlgebra))
  let quotientSpan : Submodule (ZMod p) M.augmentationQuotient :=
    Submodule.span (ZMod p)
      (Set.range fun g : Γ =>
        M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra))
  have himage_subset :
      M.quotientMap '' (algebraSpan : Set M.completedGroupAlgebra) ⊆
        (quotientSpan : Set M.augmentationQuotient) := by
    have himage_range :
        M.quotientMap.toLinearMap ''
            (Set.range fun g : Γ =>
              (M.canonicalUnit g : M.completedGroupAlgebra)) =
          Set.range fun g : Γ =>
            M.quotientMap (M.canonicalUnit g : M.completedGroupAlgebra) := by
      ext y
      constructor
      · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨(M.canonicalUnit g : M.completedGroupAlgebra), ⟨g, rfl⟩, rfl⟩
    rintro y ⟨x, hx, rfl⟩
    have hximage :
        M.quotientMap.toLinearMap x ∈
          Submodule.span (ZMod p)
            (M.quotientMap.toLinearMap ''
              (Set.range fun g : Γ =>
                (M.canonicalUnit g : M.completedGroupAlgebra))) :=
      (Submodule.image_span_subset_span
        M.quotientMap.toLinearMap
        (Set.range fun g : Γ =>
          (M.canonicalUnit g : M.completedGroupAlgebra))) ⟨x, hx, rfl⟩
    rw [himage_range] at hximage
    simpa [quotientSpan] using hximage
  apply Set.eq_univ_iff_forall.mpr
  intro y
  rcases M.quotientMap_surjective y with ⟨x, rfl⟩
  have hx : x ∈ closure (algebraSpan : Set M.completedGroupAlgebra) := by
    rw [show closure (algebraSpan : Set M.completedGroupAlgebra) = Set.univ by
      simpa [DCCore.DenseAlgebraSpan,
        algebraSpan] using hdense]
    exact Set.mem_univ x
  have hquotient_image :
      M.quotientMap x ∈
        closure (M.quotientMap '' (algebraSpan : Set M.completedGroupAlgebra)) :=
    mem_closure_image M.quotientMap_continuous.continuousAt hx
  exact closure_mono himage_subset hquotient_image

/-- At level `0`, the quotient map kills every element: the kernel is `I ^ 0 = ⊤`. -/
lemma DCCore.quotmap_eqzero_levelzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n = 0)
    (x : M.completedGroupAlgebra) :
    letI := M.instRing
    letI := M.instAlgebra
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap x = 0 := by
  subst n
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hxker : x ∈ RingHom.ker M.quotientMap.toRingHom := by
    rw [
      show RingHom.ker M.quotientMap.toRingHom = M.augmentationIdeal ^ 0 from
        M.quotientMap_ker]
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    trivial
  exact RingHom.mem_ker.mp hxker

/-- At level `0`, every canonical element has trivial `u_g - 1` image in the quotient. -/
lemma DCCore.quotmap_unitsubeq_zerolevelzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n = 0)
    (g : Γ) :
    letI := M.instRing
    letI := M.instAlgebra
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) = 0 := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact M.quotmap_eqzero_levelzero (s := s) (n := n) hn
    ((M.canonicalUnit g : M.completedGroupAlgebra) - 1)

/-- The bounded-expansion condition is automatic at truncation level `0`. -/
lemma DCCore.canonunit_subonebounded_spanlevelzero
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n = 0) :
    M.CanonunitSuboneBoundedspan := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  intro g
  have hzero :
      M.quotientMap ((M.canonicalUnit g : M.completedGroupAlgebra) - 1) = 0 :=
    M.quotmap_unitsubeq_zerolevelzero
      (s := s) (n := n) hn g
  rw [hzero]
  exact M.bounded_aug_wordspan.zero_mem

/-- Every canonical group-like element is congruent to `1` modulo the core augmentation ideal. -/
lemma DCCore.canonunit_subone_memaugideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (x : Γ) :
    letI := M.instRing
    (M.canonicalUnit x : M.completedGroupAlgebra) - 1 ∈ M.augmentationIdeal := by
  letI := M.instRing
  letI := M.instAlgebra
  rw [show M.augmentationIdeal = RingHom.ker M.augmentationMap.toRingHom from
    M.augmentation_ideal_ker]
  change
    M.augmentationMap.toRingHom
        ((M.canonicalUnit x : M.completedGroupAlgebra) - 1) = 0
  have hxaug :
      M.augmentationMap.toRingHom (M.canonicalUnit x : M.completedGroupAlgebra) = 1 := by
    simpa using M.canonicalUnit_augmentation x
  rw [map_sub, hxaug, map_one, sub_self]

/-- The upstairs augmentation factor attached to a signed generator lies in the augmentation
ideal. -/
lemma DCCore.signedaug_factormem_augideal
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d) :
    letI := M.instRing
    (M.canonicalUnit (generatorsLetterElement s a) :
        M.completedGroupAlgebra) - 1 ∈
      M.augmentationIdeal := by
  letI := M.instRing
  letI := M.instAlgebra
  exact
    M.canonunit_subone_memaugideal
      (s := s) (n := n) (generatorsLetterElement s a)

/-- The upstairs product of the augmentation factors in a signed word lies in the corresponding
augmentation-ideal power. -/
lemma DCCore.signedaug_factorsprod_mempower
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (w : List (denseSignedLetter d)) :
    letI := M.instRing
    (w.map fun a =>
        (M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1).prod ∈
      M.augmentationIdeal ^ w.length := by
  letI := M.instRing
  letI := M.instAlgebra
  letI : M.augmentationIdeal.IsTwoSided := by
    rw [show M.augmentationIdeal = RingHom.ker M.augmentationMap.toRingHom from
      M.augmentation_ideal_ker]
    infer_instance
  induction w with
  | nil =>
      rw [List.map_nil, List.prod_nil, List.length_nil]
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | cons a w ih =>
      let head : M.completedGroupAlgebra :=
        (M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1
      let tail : M.completedGroupAlgebra :=
        (w.map fun b =>
          (M.canonicalUnit (generatorsLetterElement s b) :
              M.completedGroupAlgebra) - 1).prod
      have hhead_one : head ∈ M.augmentationIdeal ^ 1 := by
        have hhead : head ∈ M.augmentationIdeal := by
          dsimp [head]
          exact M.signedaug_factormem_augideal
            (s := s) (n := n) a
        simpa [Submodule.pow_one] using hhead
      have htail : tail ∈ M.augmentationIdeal ^ w.length := by
        dsimp [tail]
        exact ih
      have hmul :
          head * tail ∈ M.augmentationIdeal ^ (1 + w.length) := by
        rw [Ideal.IsTwoSided.pow_add (I := M.augmentationIdeal) 1 w.length]
        exact Ideal.mul_mem_mul hhead_one htail
      simpa [head, tail, Nat.add_comm] using hmul

/-- Top-degree bounded words vanish after one more signed augmentation letter. -/
lemma DCCore.signedaug_lettermul_memspantop
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n)
    (hv : n ≤ v.1.1) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  let w : List (denseSignedLetter d) := a :: v.2.toList
  have hprod_power :
      (w.map fun b =>
          (M.canonicalUnit (generatorsLetterElement s b) :
              M.completedGroupAlgebra) - 1).prod ∈
        M.augmentationIdeal ^ w.length :=
    M.signedaug_factorsprod_mempower (s := s) (n := n) w
  have hv_len : v.2.toList.length = v.1.1 := by
    simp
  have hdegree_tail : n ≤ v.2.toList.length := by
    simpa [hv_len] using hv
  have hdegree : n ≤ w.length := by
    dsimp [w]
    exact Nat.le_trans hdegree_tail (Nat.le_succ v.2.toList.length)
  have hprod_power_n :
      (w.map fun b =>
          (M.canonicalUnit (generatorsLetterElement s b) :
              M.completedGroupAlgebra) - 1).prod ∈
        M.augmentationIdeal ^ n :=
    Ideal.pow_le_pow_right hdegree hprod_power
  have hquotient_zero :
      M.quotientMap
          ((w.map fun b =>
            (M.canonicalUnit (generatorsLetterElement s b) :
                M.completedGroupAlgebra) - 1).prod) = 0 := by
    have hker :
        (w.map fun b =>
            (M.canonicalUnit (generatorsLetterElement s b) :
                M.completedGroupAlgebra) - 1).prod ∈
          RingHom.ker M.quotientMap.toRingHom := by
      rw [
        show RingHom.ker M.quotientMap.toRingHom = M.augmentationIdeal ^ n from
          M.quotientMap_ker]
      exact hprod_power_n
    exact RingHom.mem_ker.mp hker
  have hmul_eq :
      M.signedAugmentationLetter (s := s) a *
          M.boundedAugmentationWord (s := s) (n := n) v =
        M.quotientMap
          ((w.map fun b =>
            (M.canonicalUnit (generatorsLetterElement s b) :
                M.completedGroupAlgebra) - 1).prod) := by
    dsimp [w]
    exact
      M.signedaug_lettermuleq_quotmapcons
        (s := s) (n := n) a v
  rw [hmul_eq, hquotient_zero]
  exact M.bounded_aug_wordspan.zero_mem

/-- Multiplying one bounded augmentation word by a signed augmentation letter stays in the
bounded-word span.

If the bounded word has length `< n`, the product is represented by the bounded word obtained by
prepending the new letter. If it has length exactly `n`, the product has augmentation degree at
least `n` and maps to zero in the quotient by `I^n`. -/
lemma DCCore.signedaug_lettmulboun_wordmemspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (_hn : n ≠ 0)
    (a : denseSignedLetter d)
    (v : denseBoundedIndex d n) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a *
        M.boundedAugmentationWord (s := s) (n := n) v ∈
      M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  by_cases hv : v.1.1 < n
  · exact
      M.signedaug_lettermul_memspanlt
        (s := s) (n := n) a v hv
  · have hvtop : n ≤ v.1.1 := le_of_not_gt hv
    exact
      M.signedaug_lettermul_memspantop
        (s := s) (n := n) a v hvtop

/-- Left multiplication by a signed augmentation letter preserves the bounded-word span. -/
lemma DCCore.signedaug_lettermul_memboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (a : denseSignedLetter d)
    {x : M.augmentationQuotient}
    (hx : x ∈ M.bounded_aug_wordspan) :
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.signedAugmentationLetter (s := s) a * x ∈
      M.bounded_aug_wordspan := by
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  let S : Set M.augmentationQuotient :=
    Set.range fun v : ULift.{u} (denseBoundedIndex d n) =>
      M.boundedAugmentationWord (s := s) (n := n) v.down
  have hxspan : x ∈ Submodule.span (ZMod p) S := by
    simpa [DCCore.bounded_aug_wordspan, S] using hx
  change
    M.signedAugmentationLetter (s := s) a * x ∈
      Submodule.span (ZMod p) S
  refine Submodule.span_induction
    (s := S)
    (p := fun y _ =>
      M.signedAugmentationLetter (s := s) a * y ∈
        Submodule.span (ZMod p) S)
    ?mem ?zero ?add ?smul hxspan
  · intro y hy
    rcases hy with ⟨v, rfl⟩
    simpa [S] using
      M.signedaug_lettmulboun_wordmemspan
        (s := s) (n := n) hn a v.down
  · change M.signedAugmentationLetter (s := s) a * 0 ∈
      Submodule.span (ZMod p) S
    rw [mul_zero]
    exact Submodule.zero_mem _
  · intro x y _hx _hy hx_mem hy_mem
    change M.signedAugmentationLetter (s := s) a * (x + y) ∈
      Submodule.span (ZMod p) S
    rw [mul_add]
    exact Submodule.add_mem _ hx_mem hy_mem
  · intro c x _hx hx_mem
    change M.signedAugmentationLetter (s := s) a * (c • x) ∈
      Submodule.span (ZMod p) S
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ c hx_mem

/-- The algebraic product term appearing when one more signed letter is prepended.

This is the remaining degree-growth step in the signed-word expansion. If the tail expansion is
known, multiplying by a fresh augmentation letter shifts every monomial degree up by one; terms
whose degree reaches `n` vanish in the quotient, and the surviving terms are still represented by
bounded augmentation words. -/
lemma DCCore.quotmap_signwordelem_consproductmem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (a : denseSignedLetter d)
    (w : List (denseSignedLetter d))
    (htail :
      letI := M.instRing
      letI := M.instQuotientRing
      letI := M.instQuotientAlgebra
      M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        (((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) *
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1)) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  rw [M.quotmap_signwordelem_consproducteq (s := s) (n := n) a w]
  exact
    M.signedaug_lettermul_memboundedspan
      (s := s) (n := n) hn a htail

/-- Prepending a signed letter reduces to the tail expansion plus the product-term estimate. -/
lemma DCCore.quotmapsigned_wordelementcons_subonemem
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (a : denseSignedLetter d)
    (w : List (denseSignedLetter d))
    (htail :
      letI := M.instRing
      letI := M.instQuotientRing
      letI := M.instQuotientAlgebra
      M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((M.canonicalUnit (generatorsSignedElement s (a :: w)) :
          M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hletter :
      M.quotientMap
          ((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan := by
    simpa [DCCore.signedAugmentationLetter] using
      M.signedaug_lettermem_boundedspan (s := s) (n := n) hnpos a
  have hproduct :
      M.quotientMap
          (((M.canonicalUnit (generatorsLetterElement s a) :
              M.completedGroupAlgebra) - 1) *
            ((M.canonicalUnit (generatorsSignedElement s w) :
              M.completedGroupAlgebra) - 1)) ∈
        M.bounded_aug_wordspan :=
    M.quotmap_signwordelem_consproductmem
      (s := s) (n := n) hn a w htail
  have hsum :
      M.quotientMap
          (((M.canonicalUnit (generatorsLetterElement s a) :
              M.completedGroupAlgebra) - 1) *
            ((M.canonicalUnit (generatorsSignedElement s w) :
              M.completedGroupAlgebra) - 1)) +
        M.quotientMap
          ((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) +
        M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan :=
    M.bounded_aug_wordspan.add_mem
      (M.bounded_aug_wordspan.add_mem hproduct hletter)
      htail
  have hidentity :
      (M.canonicalUnit (generatorsSignedElement s (a :: w)) :
          M.completedGroupAlgebra) - 1 =
        ((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) *
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) +
        ((M.canonicalUnit (generatorsLetterElement s a) :
            M.completedGroupAlgebra) - 1) +
        ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) := by
    simp only [generatorsSignedElement, List.map_cons, List.prod_cons]
    simp only [map_mul, Units.val_mul]
    noncomm_ring
  rw [hidentity]
  simpa [map_add] using hsum

/-- The truncated augmentation expansion for one concrete signed word.

For a word `a₁ ... a_m`, expand
`u_{a₁ ... a_m} - 1 = ∏ᵢ (1 + (u_{aᵢ} - 1)) - 1`. Terms of degree at most `n` are represented by
bounded augmentation words; terms of degree at least `n` map to zero modulo `I^n`, because each
letter `u_a - 1` lies in the augmentation ideal. This is the algebraic half of the generated
subgroup argument, separated from the group-theoretic signed-word representation. -/
lemma DCCore.quotmap_signedwordone_memboundedspan
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (hn : n ≠ 0)
    (w : List (denseSignedLetter d)) :
    letI := M.instRing
    letI := M.instQuotientRing
    letI := M.instQuotientAlgebra
    M.quotientMap
        ((M.canonicalUnit (generatorsSignedElement s w) :
          M.completedGroupAlgebra) - 1) ∈
      M.bounded_aug_wordspan := by
  induction w with
  | nil =>
      exact M.quotmapsigned_wordelementnil_subonemem (s := s) (n := n)
  | cons a w ih =>
      exact M.quotmapsigned_wordelementcons_subonemem
        (s := s) (n := n) hn a w ih

/-- The signed-word expansion proves the positive dense-subgroup containment. -/
lemma DCCore.posdense_subgroupspan_signedwords
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    M.PosdenseSubgroupsubOneboundedspan := by
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  intro hn g hg
  rcases generators_element_closure
      (s := s) hg with ⟨w, hw⟩
  have hword :
      M.quotientMap
          ((M.canonicalUnit (generatorsSignedElement s w) :
            M.completedGroupAlgebra) - 1) ∈
        M.bounded_aug_wordspan :=
    M.quotmap_signedwordone_memboundedspan
      (s := s) (n := n) hn w
  simpa [hw] using hword

/-- A positive-level dense-subgroup expansion extends to every group element. -/
lemma DCCore.posunit_subspan_densesubgroup
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (H : M.PosdenseSubgroupsubOneboundedspan) :
    M.PoscanonUnitsubOneboundedspan := by
  letI := M.instRing
  letI := M.instAlgebra
  letI := M.instUniformSpace
  letI := M.topologicalRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  letI := M.quotientTopology
  letI := M.quotientTopologicalRing
  intro hn g
  let f : Γ → M.augmentationQuotient := fun x =>
    M.quotientMap ((M.canonicalUnit x : M.completedGroupAlgebra) - 1)
  have hcanonical :
      Continuous fun x : Γ => (M.canonicalUnit x : M.completedGroupAlgebra) := by
    exact Units.continuous_val.comp M.canonicalUnit_continuous
  have hf : Continuous f := by
    have hsub :
        Continuous fun x : Γ =>
          (M.canonicalUnit x : M.completedGroupAlgebra) - 1 := by
      exact hcanonical.sub continuous_const
    exact M.quotientMap_continuous.comp hsub
  have hclosed_span :
      IsClosed (M.bounded_aug_wordspan : Set M.augmentationQuotient) :=
    M.closed_boundedaug_wordspan (s := s) (n := n)
  have hclosed_preimage :
      IsClosed (f ⁻¹' (M.bounded_aug_wordspan : Set M.augmentationQuotient)) :=
    hclosed_span.preimage hf
  have hdense :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) = Set.univ := by
    simpa [Subgroup.topologicalClosure_coe] using
      congrArg (fun H : Subgroup Γ => (H : Set Γ)) hs
  have hsubset :
      ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹' (M.bounded_aug_wordspan : Set M.augmentationQuotient) := by
    intro x hx
    exact H hn x hx
  have hclosure_subset :
      closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) ⊆
        f ⁻¹' (M.bounded_aug_wordspan : Set M.augmentationQuotient) :=
    closure_minimal hsubset hclosed_preimage
  have hg :
      g ∈ closure ((Subgroup.closure (Set.range s) : Subgroup Γ) : Set Γ) := by
    rw [hdense]
    exact Set.mem_univ g
  exact hclosure_subset hg

/-- The unrestricted bounded-expansion condition is equivalent to its positive-level part. -/
lemma DCCore.canonunit_subonebounded_spaniffpos
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n) :
    M.CanonunitSuboneBoundedspan ↔
      M.PoscanonUnitsubOneboundedspan := by
  constructor
  · intro H _hn
    exact H
  · intro H
    by_cases hn : n = 0
    · exact M.canonunit_subonebounded_spanlevelzero (s := s) (n := n) hn
    · exact H hn

/-- Positive raw inputs imply the original raw inputs. -/
lemma DCCore.boundedword_spanrawinputs_posrawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (H : M.BoundedwordSpanposRawinputs) :
    M.BoundedWordspanRawinputs := by
  refine ⟨H.1, ?_⟩
  rw [M.canonunit_subonebounded_spaniffpos (s := s) (n := n)]
  exact M.posunit_subspan_densesubgroup
    (s := s) (n := n) H.2

/-- Raw bounded-word inputs imply the proof inputs used by the formal spanning argument. -/
lemma DCCore.boundedword_spanproof_inputsrawinputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (M : DCCore (p := p) (Γ := Γ) s hs n)
    (H : M.BoundedWordspanRawinputs) :
    M.BoundedWordspanProofinputs := by
  refine ⟨M.densecanon_unitquot_spanalgspan
    (s := s) (n := n) H.1, ?_⟩
  letI := M.instRing
  letI := M.instQuotientRing
  letI := M.instQuotientAlgebra
  exact H.2

/-- Combine algebra-level density with the signed-word expansion to get the positive raw inputs. -/
lemma
    completed_core_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      M.BoundedwordSpanposRawinputs := by
  rcases dense_core_span
      (p := p) (Γ := Γ) s hs n with ⟨M, hdense⟩
  exact ⟨M, hdense,
    M.posdense_subgroupspan_signedwords
      (s := s) (n := n)⟩

/-- The original raw inputs follow from the positive-level dense-subgroup raw inputs.

This lemma keeps downstream finite-span arguments unchanged while making the remaining
finite-control obstruction more precise: after this point, no argument has to reprove the formal
`n = 0` quotient collapse or the closedness/density extension from the generated subgroup to all of
`Γ`. -/
lemma dense_core_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      M.BoundedWordspanRawinputs := by
  rcases
      completed_core_inputs
      (p := p) (Γ := Γ) s hs n with ⟨M, H⟩
  exact ⟨M, M.boundedword_spanrawinputs_posrawinputs H⟩

/-- The proof inputs for the bounded-word span exist for the canonical completed core.

This is now a formal consequence of the raw inputs: algebra-level canonical-unit density descends
through the continuous surjective quotient map, and the bounded expansion input is unchanged. -/
lemma core_proof_inputs
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      M.BoundedWordspanProofinputs := by
  rcases dense_core_inputs
      (p := p) (Γ := Γ) s hs n with ⟨M, H⟩
  exact ⟨M, M.boundedword_spanproof_inputsrawinputs H⟩

/-- Dense generators give the concrete bounded-word span in the augmentation quotient.

This is the finite-level algebraic frontier in its most explicit form. The proof should show that
the images of all elements of the dense subgroup generated by `s` reduce modulo `I^n` to
`ZMod p`-linear combinations of bounded products of the signed augmentation letters
`s i - 1` and `(s i)⁻¹ - 1`, and then use continuity/density to pass from the dense subgroup
algebra to the completed group algebra quotient. -/
lemma core_bounded_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      M.BoundedAugWordspan := by
  rcases core_proof_inputs
      (p := p) (Γ := Γ) s hs n with ⟨M, H⟩
  exact ⟨M, M.bounded_wordspan_proofinputs H⟩

/-- Dense generators give a finite spanning family for the augmentation quotient.

This is now the finite-level algebraic frontier. The proof should construct the finite set of
bounded words in the dense generators, show every group-like element reduces modulo `I^n` to a
`ZMod p`-linear combination of those words, and then use density to extend the spanning statement
to all of `ZMod p[[Γ]] / I^n`. -/
lemma generators_core_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      M.FinDenseWordspan := by
  rcases core_bounded_span
      (p := p) (Γ := Γ) s hs n with ⟨M, hspan⟩
  exact ⟨M, M.findense_wordspan_boundedwordspan hspan⟩

/-- Dense finite generators make the augmentation quotient finite.

This is the second half of the remaining frontier. Starting from the completed group algebra core,
the dense tuple `s : Fin d → Γ` should imply that the quotient
`ZMod p[[Γ]] / I^n` is finite: modulo `I^n`, the algebra is spanned over `ZMod p` by bounded-length
monomials in the finitely many elements `s i - 1`.

The remaining work is the finite-dimensional dense-generator argument. -/
lemma
  completed_core_span
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    (n : ℕ) :
    ∃ M : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient := by
  rcases generators_core_span
      (p := p) (Γ := Γ) s hs n with ⟨M, hspan⟩
  exact ⟨M, M.finaug_quotfin_densewordspan hspan⟩

/-- Repackage a completed-group-algebra core together with its Jennings-Lazard identification as
the flatter model interface.

This is only bookkeeping: the core already contains the ambient completed algebra, augmentation,
`I^n` quotient, unit reduction, and induced map from `Γ`; the Jennings-Lazard package supplies the
range equivalence and the kernel calculation.  Keeping this conversion explicit makes the remaining
mathematical obstruction visible: one still has to construct a single core that has both the
finite/discrete control and the Jennings-Lazard identification. -/
noncomputable def DCModel.ofCore
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (J : DenseLazardIdentification C) :
    DCModel (p := p) (Γ := Γ) s hs n :=
  C.toModel J

/-- Finiteness and discreteness transfer unchanged across `ofCore`.

The model conversion does not alter the quotient algebra or the image of the quotient-unit map; it
only copies fields out of the core and appends the Jennings-Lazard equivalence. -/
lemma model_discrete_core
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (J : DenseLazardIdentification C)
    (hfinite : Finite C.augmentationQuotient)
    (hdiscrete :
      letI := C.quotientTopology
      DiscreteTopology C.quotientUnitMap.range) :
    ∃ M : DCModel
        (p := p) (Γ := Γ) s hs n,
      Finite M.augmentationQuotient ∧
        (letI := M.quotientTopology
        DiscreteTopology M.quotientUnitMap.range) := by
  let M : DCModel
      (p := p) (Γ := Γ) s hs n :=
    DCModel.ofCore
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C J
  refine ⟨M, ?_, ?_⟩
  · dsimp [M, DCModel.ofCore]
    exact hfinite
  · dsimp [M, DCModel.ofCore]
    exact hdiscrete

/-- Bounded augmentation words plus the positive Jennings input give the requested same-core
finite/discrete Jennings-Lazard package.

This is only a packaging lemma: the bounded-word span gives finiteness of the augmentation
quotient, finiteness plus Hausdorffness makes the quotient-unit range discrete, and the positive
Jennings input supplies the Jennings-Lazard identification for the very same core. -/
lemma DCCore.findiscrete_rangjennspan_posjenninpu
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (C : DCCore (p := p) (Γ := Γ) s hs n)
    (hbounded : C.BoundedAugWordspan)
    (hpositive : C.PosJenningsInput) :
    Finite C.augmentationQuotient ∧
      (letI := C.quotientTopology
      DiscreteTopology C.quotientUnitMap.range) ∧
      Nonempty (DenseLazardIdentification C) := by
  have hfinite : Finite C.augmentationQuotient :=
    C.finaug_quotbounded_augwordspan
      (s := s) (n := n) hbounded
  have hdiscrete :
      letI := C.quotientTopology
      DiscreteTopology C.quotientUnitMap.range :=
    C.discretequot_unitmap_finaugquot
      (s := s) (n := n) hfinite
  have hinput : JLInput C := by
    refine ⟨?_⟩
    intro _hn
    exact
      (DCCore.posjennings_inputiffpos_dimsubgboun
        (p := p) (Γ := Γ) (s := s) (hs := hs) C).1 hpositive
  have hJ : Nonempty (DenseLazardIdentification C) :=
    generators_lazard_identification
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n) C hinput
  exact ⟨hfinite, hdiscrete, hJ⟩

/-- Same-core bounded span and positive Jennings input imply the target package. -/
lemma gens_completed_input
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} {s : Fin d → Γ}
    {hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤}
    {n : ℕ}
    (h :
      ∃ C : DCCore
          (p := p) (Γ := Γ) s hs n,
        C.BoundedAugWordspan ∧ C.PosJenningsInput) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite C.augmentationQuotient ∧
        (letI := C.quotientTopology
        DiscreteTopology C.quotientUnitMap.range) ∧
        Nonempty (DenseLazardIdentification C) := by
  rcases h with ⟨C, hbounded, hpositive⟩
  exact
    ⟨C,
      C.findiscrete_rangjennspan_posjenninpu
        (s := s) (n := n) hbounded hpositive⟩

/-- The same-core target is complete at levels `0` and `1`.

At these levels the Zassenhaus filtration is all of `Γ`, so the positive Jennings implication is
vacuous after choosing the bounded-word core. -/
lemma gens_completed_identification
    {p : ℕ} [Fact p.Prime]
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    {d : ℕ} (s : Fin d → Γ)
    (hs : Subgroup.topologicalClosure (Subgroup.closure (Set.range s)) = ⊤)
    {n : ℕ} (hn : n ≤ 1) :
    ∃ C : DCCore
        (p := p) (Γ := Γ) s hs n,
      Finite C.augmentationQuotient ∧
        (letI := C.quotientTopology
        DiscreteTopology C.quotientUnitMap.range) ∧
        Nonempty (DenseLazardIdentification C) := by
  rcases core_bounded_span
      (p := p) (Γ := Γ) s hs n with
    ⟨C, hbounded⟩
  have hpositive : C.PosJenningsInput := by
    intro g _hmem
    exact zassenhaus_filtration_one p Γ hn g
  exact
    gens_completed_input
      (p := p) (Γ := Γ) (s := s) (hs := hs) (n := n)
      ⟨C, hbounded, hpositive⟩

/-!
The bounded-word endgame intentionally stops here. Positive Jennings input for
Golod-Shafarevich should be obtained from continuous finite p-group quotients of
the pro-p group, rather than from automatic continuity of arbitrary finite-index
subgroups.
-/

end Towers
