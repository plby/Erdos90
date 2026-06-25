import Submission.Algebra.DenseGenerators.FiniteGroupAlgebra


open scoped Topology Pointwise

noncomputable section

namespace Submission

universe u

/-- The first-order linearization of a finite group algebra of an elementary abelian `p`-group.

It sends a basis element `[x]` to the corresponding additive group element. Since the target has
exponent `p`, the augmentation square is killed by this map. -/
noncomputable def denseGeneratorsLinear
    (p : ℕ) [Fact p.Prime]
    (Λ : Type u) [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)] :
    denseGroupAlgebra p Λ →ₗ[ZMod p] Additive Λ :=
  Finsupp.lsum (ZMod p)
    (fun x : Λ =>
      (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p).smulRight (Additive.ofMul x))

@[simp]
lemma dense_generators_single
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)]
    (x : Λ) (c : ZMod p) :
    denseGeneratorsLinear p Λ
        (MonoidAlgebra.single x c : denseGroupAlgebra p Λ) =
      c • Additive.ofMul x := by
  change Finsupp.lsum (S := ZMod p)
      (fun x : Λ =>
        (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p).smulRight (Additive.ofMul x))
      (Finsupp.single x c) = c • Additive.ofMul x
  exact
    Finsupp.lsum_single (S := ZMod p)
      (f := fun x : Λ =>
        (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p).smulRight (Additive.ofMul x)) x c

@[simp]
lemma dense_first_element
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)]
    (x : Λ) :
    denseGeneratorsLinear p Λ
        (denseGeneratorsElement p Λ x) =
      Additive.ofMul x := by
  change
    denseGeneratorsLinear p Λ
        (MonoidAlgebra.single x (1 : ZMod p) :
          denseGroupAlgebra p Λ) =
      Additive.ofMul x
  simp

@[simp]
lemma dense_generators_linear
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)] :
    denseGeneratorsLinear p Λ
        (1 : denseGroupAlgebra p Λ) =
      0 := by
  rw [MonoidAlgebra.one_def]
  simp

@[simp]
lemma dense_generators_sub
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)]
    (x : Λ) :
    denseGeneratorsLinear p Λ
        (denseGeneratorsElement p Λ x - 1) =
      Additive.ofMul x := by
  simp

/-- The first-order linearization kills every length-two augmentation word. -/
lemma dense_generators_first
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)]
    (w : List.Vector Λ 2) :
    denseGeneratorsLinear p Λ
        (denseGeneratorsGenerator p Λ w) =
      0 := by
  rcases w with ⟨xs, hxs⟩
  cases xs with
  | nil =>
      simp at hxs
  | cons a xs =>
    cases xs with
    | nil =>
        simp at hxs
    | cons b xs =>
      cases xs with
      | cons c xs =>
          simp at hxs
      | nil =>
          let A : denseGroupAlgebra p Λ :=
            denseGeneratorsElement p Λ a
          let B : denseGroupAlgebra p Λ :=
            denseGeneratorsElement p Λ b
          have hprod : (A - 1) * (B - 1) = A * B - A - B + 1 := by
            noncomm_ring
          have htolist :
              List.Vector.toList (⟨[a, b], hxs⟩ : List.Vector Λ 2) = [a, b] := rfl
          rw [denseGeneratorsGenerator, htolist]
          simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
          rw [mul_one]
          change
            denseGeneratorsLinear p Λ ((A - 1) * (B - 1)) = 0
          rw [hprod]
          dsimp [A, B, denseGeneratorsElement]
          simp only [MonoidAlgebra.single_mul_single, one_mul, map_add, map_sub,
            dense_generators_single,
            dense_generators_linear]
          simp [sub_eq_add_neg, add_assoc]

/-- The first-order linearization kills the span of length-two augmentation words. -/
lemma dense_generators_two
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)]
    {z : denseGroupAlgebra p Λ}
    (hz : z ∈ denseGeneratorsSpan p Λ 2) :
    denseGeneratorsLinear p Λ z = 0 := by
  let T : Set (denseGroupAlgebra p Λ) :=
    { y | ∃ w : List.Vector Λ 2,
        denseGeneratorsGenerator p Λ w = y }
  have hzspan : z ∈ Submodule.span (ZMod p) T := by
    simpa [denseGeneratorsSpan, T] using hz
  refine Submodule.span_induction
    (s := T)
    (p := fun y _ => denseGeneratorsLinear p Λ y = 0)
    ?mem ?zero ?add ?smul hzspan
  · rintro y ⟨w, rfl⟩
    exact
      dense_generators_first
        (p := p) (Λ := Λ) w
  · simp
  · intro x y _hx _hy hx0 hy0
    simp [hx0, hy0]
  · intro c x _hx hx0
    simp [hx0]

/-- The first-order linearization kills the square of the augmentation ideal. -/
lemma dense_generators_sq
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)]
    {z : denseGroupAlgebra p Λ}
    (hz : z ∈ denseGeneratorsIdeal p Λ ^ 2) :
    denseGeneratorsLinear p Λ z = 0 := by
  have hzword :
      z ∈ denseGeneratorsSpan p Λ (1 + 1) :=
    (dense_algebra_span
      (p := p) (Λ := Λ) (n := 1) (x := z)).1 (by simpa using hz)
  exact
    dense_generators_two
      (p := p) (Λ := Λ) (by simpa using hzword)

/-- In an elementary abelian `p`-group, no nontrivial basis element is congruent to `1` modulo
the square of the augmentation ideal. -/
lemma element_sq_comm
    {p : ℕ} [Fact p.Prime]
    {Λ : Type u} [CommGroup Λ]
    [Module (ZMod p) (Additive Λ)]
    {x : Λ}
    (hx :
      denseGeneratorsElement p Λ x - 1 ∈
        denseGeneratorsIdeal p Λ ^ 2) :
    x = 1 := by
  have hmap :
      denseGeneratorsLinear p Λ
          (denseGeneratorsElement p Λ x - 1) =
        0 :=
    dense_generators_sq
      (p := p) (Λ := Λ) hx
  rw [dense_generators_sub] at hmap
  change Additive.ofMul x = Additive.ofMul (1 : Λ) at hmap
  exact Additive.ofMul.injective hmap

end Submission
