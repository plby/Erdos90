import Submission.Group.HallBasic.Polynomial
import Submission.Group.LowerAssociatedGraded

noncomputable section

namespace Submission
namespace HallTree

open TBluepr

universe u

variable {α : Type u}

/-- The zero-based lower-central degrees of two Hall trees add under bracketing. -/
theorem lower_bracket_degree
    (u v : HallTree α) :
    (u.weight - 1) + (v.weight - 1) + 1 =
      (commutator u v).weight - 1 := by
  simp only [weight_commutator]
  have hu := u.weight_pos
  have hv := v.weight_pos
  omega

/-- The existing Hall-tree class is the generic lower-central class of its representative. -/
theorem free_lower_class
    (w : HallTree α) :
    w.freeCentralLayer =
      TBluepr.lowerCentralClass (w.weight - 1)
        w.freeCentralRep :=
  rfl

/--
Evaluation of a Hall-tree commutator agrees with the generic associated-graded
bracket of the classes of its two children.
-/
theorem free_layer_commutator
    (u v : HallTree α) :
    (commutator u v).freeCentralLayer =
      TBluepr.lowerBracketClass
        (u.weight - 1) (v.weight - 1)
        ((commutator u v).weight - 1)
        (lower_bracket_degree u v)
        u.freeCentralLayer v.freeCentralLayer := by
  rw [free_lower_class,
    free_lower_class,
    free_lower_class,
    TBluepr.lower_bracket_class]
  rfl

/--
Fixed-weight form of `free_layer_commutator`, matching the
classes used by the Hall basis predicates.
-/
theorem free_central_commutator
    {n : ℕ}
    (u v : HallTree α)
    (hweight : (commutator u v).weight = n) :
    (commutator u v).freeLowerWeight hweight =
      TBluepr.lowerBracketClass
        (u.weight - 1) (v.weight - 1) (n - 1)
        (by
          rw [← hweight]
          exact lower_bracket_degree u v)
        u.freeCentralLayer v.freeCentralLayer := by
  subst n
  simpa [freeLowerWeight] using
    free_layer_commutator u v

/--
Compositional fixed-weight form of the Hall-tree commutator bridge.  The two
child weights and the output weight are supplied explicitly.
-/
theorem free_lower_weights
    {i j n : ℕ}
    (u v : HallTree α)
    (hu : u.weight = i)
    (hv : v.weight = j)
    (hadd : i + j = n) :
    (commutator u v).freeLowerWeight
        (by simpa only [weight_commutator, hu, hv] using hadd) =
      TBluepr.lowerBracketClass
        (i - 1) (j - 1) (n - 1)
        (by
          have huPos := u.weight_pos
          have hvPos := v.weight_pos
          omega)
        (u.freeLowerWeight hu)
        (v.freeLowerWeight hv) := by
  subst i
  subst j
  subst n
  simpa [freeLowerWeight] using
    free_layer_commutator u v

/-- The zero-based degree of a left-normed triple Hall bracket. -/
theorem lower_triple_degree
    (u v w : HallTree α) :
    ((u.weight - 1) + (v.weight - 1) + 1) + (w.weight - 1) + 1 =
      (commutator (commutator u v) w).weight - 1 := by
  simp only [weight_commutator]
  have hu := u.weight_pos
  have hv := v.weight_pos
  have hw := w.weight_pos
  omega

/--
Fixed-weight evaluation of a left-normed Hall-tree triple agrees with the
generic nested lower-central bracket.
-/
theorem free_lower_commutator
    {n : ℕ}
    (u v w : HallTree α)
    (hweight : (commutator (commutator u v) w).weight = n) :
    (commutator (commutator u v) w).freeLowerWeight
        hweight =
      TBluepr.lowerTripleClass
        (u.weight - 1) (v.weight - 1) (w.weight - 1) (n - 1)
        (by
          rw [← hweight]
          exact lower_triple_degree u v w)
        u.freeCentralLayer v.freeCentralLayer
        w.freeCentralLayer := by
  subst n
  change (commutator (commutator u v) w).freeCentralLayer = _
  rw [free_lower_class,
    free_lower_class,
    free_lower_class,
    free_lower_class,
    TBluepr.lower_triple_class]
  rfl

/--
Compositional fixed-weight form of a left-normed Hall-tree triple.  The inner
and outer output weights are supplied explicitly, so the same intermediate
layer can be used after permuting inputs.
-/
theorem free_commutator_weights
    {i j p k n : ℕ}
    (u v w : HallTree α)
    (hu : u.weight = i)
    (hv : v.weight = j)
    (hinner : i + j = p)
    (hw : w.weight = k)
    (houter : p + k = n) :
    (commutator (commutator u v) w).freeLowerWeight
        (by simpa only [weight_commutator, hu, hv, hw] using
          hinner ▸ houter) =
      TBluepr.lowerBracketClass
        (p - 1) (k - 1) (n - 1)
        (by
          have huPos := u.weight_pos
          have hvPos := v.weight_pos
          have hwPos := w.weight_pos
          omega)
        (TBluepr.lowerBracketClass
          (i - 1) (j - 1) (p - 1)
          (by
            have huPos := u.weight_pos
            have hvPos := v.weight_pos
            omega)
          (u.freeLowerWeight hu)
          (v.freeLowerWeight hv))
        (w.freeLowerWeight hw) := by
  rw [free_lower_weights
    (commutator u v) w
    (by simpa only [weight_commutator, hu, hv] using hinner) hw houter]
  rw [free_lower_weights
    u v hu hv hinner]

/-- Swapping the children of a Hall-tree bracket negates its graded class. -/
theorem free_lower_swap
    (u v : HallTree α) :
    (commutator u v).freeLowerWeight rfl =
      -(commutator v u).freeLowerWeight
        (by
          simp only [weight_commutator]
          omega) := by
  rw [free_central_commutator,
    free_central_commutator]
  exact TBluepr.central_bracket_skew
    (u.weight - 1) (v.weight - 1) ((commutator u v).weight - 1)
    (lower_bracket_degree u v)
    (by
      simp only [weight_commutator]
      have hu := u.weight_pos
      have hv := v.weight_pos
      omega)
    u.freeCentralLayer v.freeCentralLayer

/-- Transported form of bracket skew-symmetry in an explicitly chosen weight. -/
theorem free_commutator_swap
    {n : ℕ}
    (u v : HallTree α)
    (hweight : (commutator u v).weight = n) :
    (commutator u v).freeLowerWeight hweight =
      -(commutator v u).freeLowerWeight
        (by
          simp only [weight_commutator] at hweight ⊢
          omega) := by
  subst n
  simpa only using free_lower_swap u v

/-- A Hall-tree self-bracket vanishes in the associated-graded layer. -/
@[simp]
theorem free_lower_self
    (u : HallTree α) :
    (commutator u u).freeLowerWeight rfl = 0 := by
  rw [free_central_commutator,
    free_lower_class,
    TBluepr.lower_bracket_class]
  simp only [commutatorElement_self]
  exact TBluepr.lower_central_one _

/-- Transported form of self-bracket vanishing in an explicitly chosen weight. -/
@[simp]
theorem free_commutator_self
    {n : ℕ}
    (u : HallTree α)
    (hweight : (commutator u u).weight = n) :
    (commutator u u).freeLowerWeight hweight = 0 := by
  subst n
  simpa only using free_lower_self u

/-- The fixed-weight Hall-tree classes satisfy Jacobi. -/
theorem free_lower_jacobi
    (u v w : HallTree α) :
    (commutator (commutator u v) w).freeLowerWeight rfl +
        (commutator (commutator v w) u).freeLowerWeight
          (by
            simp only [weight_commutator]
            omega) +
      (commutator (commutator w u) v).freeLowerWeight
        (by
          simp only [weight_commutator]
          omega) =
      0 := by
  rw [free_lower_commutator,
    free_lower_commutator,
    free_lower_commutator]
  exact TBluepr.central_triple_jacobi
    (u.weight - 1) (v.weight - 1) (w.weight - 1)
    ((commutator (commutator u v) w).weight - 1)
    (lower_triple_degree u v w)
    (by
      simp only [weight_commutator]
      have hu := u.weight_pos
      have hv := v.weight_pos
      have hw := w.weight_pos
      omega)
    (by
      simp only [weight_commutator]
      have hu := u.weight_pos
      have hv := v.weight_pos
      have hw := w.weight_pos
      omega)
    u.freeCentralLayer v.freeCentralLayer
      w.freeCentralLayer

/--
Swapping the first two inputs of a left-normed Hall-tree triple negates its
graded class.
-/
theorem commutator_swap_inner
    (u v w : HallTree α) :
    (commutator (commutator u v) w).freeLowerWeight rfl =
      -(commutator (commutator v u) w).freeLowerWeight
        (by
          simp only [weight_commutator]
          omega) := by
  let p := u.weight + v.weight
  let n := p + w.weight
  let uv :
      Additive
        (LowerGradedLayer (FreeGroup α) (p - 1)) :=
    TBluepr.lowerBracketClass
      (u.weight - 1) (v.weight - 1) (p - 1) (by
        dsimp only [p]
        have hu := u.weight_pos
        have hv := v.weight_pos
        omega)
      u.freeCentralLayer v.freeCentralLayer
  let vu :
      Additive
        (LowerGradedLayer (FreeGroup α) (p - 1)) :=
    TBluepr.lowerBracketClass
      (v.weight - 1) (u.weight - 1) (p - 1) (by
        dsimp only [p]
        have hu := u.weight_pos
        have hv := v.weight_pos
        omega)
      v.freeCentralLayer u.freeCentralLayer
  let outer :
      Additive
          (LowerGradedLayer (FreeGroup α) (p - 1)) →
        Additive
          (LowerGradedLayer (FreeGroup α) (n - 1)) :=
    fun x =>
      TBluepr.lowerBracketClass
        (p - 1) (w.weight - 1) (n - 1) (by
          dsimp only [n]
          have hp : 0 < p := by
            dsimp only [p]
            have hu := u.weight_pos
            omega
          have hw := w.weight_pos
          omega)
        x w.freeCentralLayer
  have hleft :
      (commutator (commutator u v) w).freeLowerWeight rfl =
        outer uv := by
    dsimp only [outer, uv, p, n]
    convert
      free_commutator_weights
        (i := u.weight) (j := v.weight) (p := p)
        (k := w.weight) (n := n)
        u v w rfl rfl (by simp only [p]) rfl (by simp only [n]) using 1
  have hright :
      (commutator (commutator v u) w).freeLowerWeight
          (by
            simp only [weight_commutator]
            omega) =
        outer vu := by
    dsimp only [outer, vu, p, n]
    convert
      free_commutator_weights
        (i := v.weight) (j := u.weight) (p := p)
        (k := w.weight) (n := n)
        v u w rfl rfl (by
          dsimp only [p]
          omega) rfl (by simp only [n]) using 1
  have hinner : uv = -vu := by
    dsimp only [uv]
    exact TBluepr.central_bracket_skew
      (u.weight - 1) (v.weight - 1) (p - 1)
      (by
        dsimp only [p]
        have hu := u.weight_pos
        have hv := v.weight_pos
        omega)
      (by
        dsimp only [p]
        have hu := u.weight_pos
        have hv := v.weight_pos
        omega)
      u.freeCentralLayer v.freeCentralLayer
  have houter : outer (-vu) = -outer vu := by
    dsimp only [outer]
    exact TBluepr.bracket_neg_left
      (p - 1) (w.weight - 1) (n - 1) (by
        dsimp only [n]
        have hp : 0 < p := by
          dsimp only [p]
          have hu := u.weight_pos
          omega
        have hw := w.weight_pos
        omega)
      vu w.freeCentralLayer
  calc
    (commutator (commutator u v) w).freeLowerWeight rfl =
        outer uv := hleft
    _ = outer (-vu) := by rw [hinner]
    _ = -outer vu := houter
    _ =
        -(commutator (commutator v u) w).freeLowerWeight
          (by
            simp only [weight_commutator]
            omega) := by rw [hright]

/-- Transported form of inner skew-symmetry in an explicitly chosen total weight. -/
theorem free_swap_inner
    {n : ℕ}
    (u v w : HallTree α)
    (hweight : (commutator (commutator u v) w).weight = n) :
    (commutator (commutator u v) w).freeLowerWeight
        hweight =
      -(commutator (commutator v u) w).freeLowerWeight
        (by
          simp only [weight_commutator] at hweight ⊢
          omega) := by
  subst n
  simpa only using
    commutator_swap_inner
      u v w

/--
Jacobi rewrite used by Hall normalization:
`[[u,v],w] = [[u,w],v] - [[v,w],u]` in the associated graded.
-/
theorem lower_jacobi_rewrite
    (u v w : HallTree α) :
    (commutator (commutator u v) w).freeLowerWeight rfl =
      (commutator (commutator u w) v).freeLowerWeight
          (by
            simp only [weight_commutator]
            omega) -
        (commutator (commutator v w) u).freeLowerWeight
          (by
            simp only [weight_commutator]
            omega) := by
  have hjacobi := free_lower_jacobi u v w
  have hswap :=
    free_swap_inner
      w u v
      (show
        (commutator (commutator w u) v).weight =
          (commutator (commutator u v) w).weight by
        simp only [weight_commutator]
        omega)
  rw [hswap] at hjacobi
  calc
    (commutator (commutator u v) w).freeLowerWeight rfl =
        ((commutator (commutator u v) w).freeLowerWeight rfl +
            (commutator (commutator v w) u).freeLowerWeight
              (by
                simp only [weight_commutator]
                omega) +
            -(commutator (commutator u w) v).freeLowerWeight
              (by
                simp only [weight_commutator]
                omega)) +
          ((commutator (commutator u w) v).freeLowerWeight
              (by
                simp only [weight_commutator]
                omega) -
            (commutator (commutator v w) u).freeLowerWeight
              (by
                simp only [weight_commutator]
                omega)) := by
      abel
    _ =
        (commutator (commutator u w) v).freeLowerWeight
            (by
              simp only [weight_commutator]
              omega) -
          (commutator (commutator v w) u).freeLowerWeight
            (by
              simp only [weight_commutator]
              omega) := by
      rw [hjacobi, zero_add]

/-- Transported form of the Jacobi rewrite in an explicitly chosen total weight. -/
theorem free_jacobi_rewrite
    {n : ℕ}
    (u v w : HallTree α)
    (hweight : (commutator (commutator u v) w).weight = n) :
    (commutator (commutator u v) w).freeLowerWeight
        hweight =
      (commutator (commutator u w) v).freeLowerWeight
          (by
            simp only [weight_commutator] at hweight ⊢
            omega) -
        (commutator (commutator v w) u).freeLowerWeight
          (by
            simp only [weight_commutator] at hweight ⊢
            omega) := by
  subst n
  simpa only using lower_jacobi_rewrite u v w

end HallTree
end Submission
