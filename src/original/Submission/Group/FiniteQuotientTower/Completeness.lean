import Submission.Group.InverseLimit
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff


open scoped Topology

noncomputable section

namespace Submission
namespace Group

universe u v

/--
A compatible finite quotient system whose finite levels also carry `T₂`
topologies.  The transition maps need not be continuous for the compactness
argument: only the coordinate maps from the compact source are used
topologically.
-/
structure tSQuotie where
  toSystem : cSQuotie.{u}
  [topologicalSpace_obj : ∀ n, TopologicalSpace (toSystem.obj n)]
  [objT2 : ∀ n, T2Space (toSystem.obj n)]

attribute [instance] tSQuotie.topologicalSpace_obj
attribute [instance] tSQuotie.objT2

namespace tSQuotie

variable
    (S : tSQuotie.{u})
    {H : Type v}
    [Group H]
    [TopologicalSpace H]

/--
The fiber at level `n` over one coherent inverse-limit thread.
-/
def inverseLimitFiber
    (f : ∀ n, H →* S.toSystem.obj n)
    (y : inverseLimit S.toSystem)
    (n : ℕ) :
    Set H :=
  {x | f n x = inverseLimitProjection S.toSystem n y}

omit [TopologicalSpace H] in
lemma inverse_limit_fiber
    (f : ∀ n, H →* S.toSystem.obj n)
    (y : inverseLimit S.toSystem)
    (n : ℕ)
    (x : H) :
    x ∈ S.inverseLimitFiber f y n ↔
      f n x = inverseLimitProjection S.toSystem n y := by
  rfl

/-- Projections from the inverse limit to finite levels are continuous for the
subtype topology inherited from the product of finite levels. -/
lemma limit_projection_continuous
    (n : ℕ) :
    Continuous (inverseLimitProjection S.toSystem n) := by
  change Continuous fun x : inverseLimit S.toSystem =>
    (x : (k : ℕ) → S.toSystem.obj k) n
  exact (continuous_apply n).comp continuous_subtype_val

/-- A compatible cone of continuous finite-level coordinates induces a
continuous inverse-limit lift. -/
lemma inverse_lift_continuous
    (f : ∀ n, H →* S.toSystem.obj n)
    (hf : ∀ n, Continuous (f n))
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.toSystem.map h).comp (f n) = f m) :
    Continuous (inverseLimitLift S.toSystem f hcompat) := by
  apply Continuous.subtype_mk
  exact continuous_pi hf

/-- Continuity of an inverse-limit lift is detected coordinatewise. -/
lemma inverse_limit_continuous
    (f : ∀ n, H →* S.toSystem.obj n)
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.toSystem.map h).comp (f n) = f m) :
    Continuous (inverseLimitLift S.toSystem f hcompat) ↔
      ∀ n, Continuous (f n) := by
  constructor
  · intro hlift n
    rw [← limit_projection_lift S.toSystem f hcompat n]
    exact (S.limit_projection_continuous n).comp hlift
  · exact fun hf => S.inverse_lift_continuous f hf hcompat

/--
Fibers of continuous finite-level coordinate maps are closed.
-/
lemma limit_fiber_closed
    (f : ∀ n, H →* S.toSystem.obj n)
    (hf : ∀ n, Continuous (f n))
    (y : inverseLimit S.toSystem)
    (n : ℕ) :
    IsClosed (S.inverseLimitFiber f y n) := by
  change IsClosed ((fun x : H => f n x) ⁻¹' {inverseLimitProjection S.toSystem n y})
  exact isClosed_singleton.preimage (hf n)

omit [TopologicalSpace H] in
/--
Surjective finite-level coordinate maps have nonempty fibers over every
coherent thread coordinate.
-/
lemma limit_fiber_nonempty
    (f : ∀ n, H →* S.toSystem.obj n)
    (hfsurj : ∀ n, Function.Surjective (f n))
    (y : inverseLimit S.toSystem)
    (n : ℕ) :
    (S.inverseLimitFiber f y n).Nonempty := by
  rcases hfsurj n (inverseLimitProjection S.toSystem n y) with
    ⟨x, hx⟩
  exact ⟨x, hx⟩

omit [TopologicalSpace H] in
/--
Compatibility of the coordinate maps and of the target thread makes the fiber
sequence decreasing.
-/
lemma limit_fiber_subset
    (f : ∀ n, H →* S.toSystem.obj n)
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.toSystem.map h).comp (f n) = f m)
    (y : inverseLimit S.toSystem)
    (n : ℕ) :
    S.inverseLimitFiber f y (n + 1) ⊆ S.inverseLimitFiber f y n := by
  intro x hx
  rw [S.inverse_limit_fiber] at hx ⊢
  have hmap := congrArg
    (fun φ : H →* S.toSystem.obj n => φ x)
    (hcompat (Nat.le_succ n))
  change S.toSystem.map (Nat.le_succ n) (f (n + 1) x) = f n x at hmap
  calc
    f n x = S.toSystem.map (Nat.le_succ n) (f (n + 1) x) := hmap.symm
    _ = S.toSystem.map (Nat.le_succ n)
        (inverseLimitProjection S.toSystem (n + 1) y) := by
      rw [hx]
    _ = inverseLimitProjection S.toSystem n y :=
      limit_projection_compat S.toSystem
        (Nat.le_succ n) y

/--
Continuous surjective finite-level coordinates from a compact group fill every
coherent thread in the inverse limit.
-/
lemma limit_compact_space
    [CompactSpace H]
    (f : ∀ n, H →* S.toSystem.obj n)
    (hf : ∀ n, Continuous (f n))
    (hfsurj : ∀ n, Function.Surjective (f n))
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.toSystem.map h).comp (f n) = f m) :
    Function.Surjective
      (inverseLimitLift S.toSystem f hcompat) := by
  intro y
  let C : ℕ → Set H := S.inverseLimitFiber f y
  have hCnonempty : ∀ n : ℕ, (C n).Nonempty := by
    intro n
    exact S.limit_fiber_nonempty f hfsurj y n
  have hCclosed : ∀ n : ℕ, IsClosed (C n) := by
    intro n
    exact S.limit_fiber_closed f hf y n
  have hCcompact0 : IsCompact (C 0) :=
    isCompact_univ.of_isClosed_subset (hCclosed 0) (Set.subset_univ _)
  rcases IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      C
      (fun n => S.limit_fiber_subset f hcompat y n)
      hCnonempty
      hCcompact0
      hCclosed with
    ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext n
  exact (S.inverse_limit_fiber f y n x).mp (Set.mem_iInter.mp hx n)

/--
The quotient of a compact source by the kernel of a complete compatible finite
quotient tower is canonically isomorphic to the inverse limit.
-/
def limitCompactSpace
    [CompactSpace H]
    (f : ∀ n, H →* S.toSystem.obj n)
    (hf : ∀ n, Continuous (f n))
    (hfsurj : ∀ n, Function.Surjective (f n))
    (hcompat : ∀ {m n : ℕ} (h : m ≤ n), (S.toSystem.map h).comp (f n) = f m) :
    H ⧸ (inverseLimitLift S.toSystem f hcompat).ker ≃*
      inverseLimit S.toSystem :=
  QuotientGroup.quotientKerEquivOfSurjective
    (inverseLimitLift S.toSystem f hcompat)
    (S.limit_compact_space f hf hfsurj hcompat)

end tSQuotie

end Group
end Submission
